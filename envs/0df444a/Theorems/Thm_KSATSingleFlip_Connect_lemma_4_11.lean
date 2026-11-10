-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_4_11
-- name    : KSATSingleFlip.Connect.lemma_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:09:27.702945+00:00
-- url     : https://prove2.me/theorems/66b27d72-3f80-487a-9c72-abdafd4163af
-- title:
--   Lemma 4.11 — comparison and concentration of the local-update flow
-- statement:
--   Fix $L\ge1$, $\vartheta\in[0,1]$; $g_v(\Phi,x)$ is the flow at $v$ of LocalUpdate on $B_L(L_x,v)$ when $v$ is $(L,k^4)$-locally tree-structured in $L_x$, and $0$ otherwise.
--
--   (i) For any formula $\Phi$, $x\in\Omega_\Phi$ and $v$ with $B_L(\Phi,v)$ a tree, the flow $\mathbb E[\mathbf 1\{y'_v\ne x_v\}/\max\{1,d_H(x,y')\}]$ of $y'\leftarrow\mathrm{LocalUpdate}(x)$ on $B_L(\Phi,v)$ is at least $g_v(\Phi,x)$, with equality when $v$ is $(L,k^4)$-locally tree-structured in $L_x$.
--
--   (ii) Given $x\in\{0,1\}^n$ and $\alpha\ge0$, let $\Phi_x$ consist of $\mathrm{Pois}(\alpha n)$ clauses sampled independently and uniformly among $k$-clauses satisfied by $x$, with forcing mean $\lambda^+ = \alpha k/(2^k-1)$ in the range of Theorem 4.8(iii), and choose $(L,\vartheta)$ according to Theorem 4.8(iii). Then there is an absolute $C>0$ such that for $b_k = \exp(-C(L+1)\ln k)$ and all $n\ge n_0(k)$,
--   $$\Pr\Big(\sum_{v\in[n]} g_v(\Phi_x,x) < \frac{\varepsilon_k n}{2}\Big)\ \le\ 3\exp(-b_k n).$$
--   In Lean, "$(L,\vartheta)$ according to Theorem 4.8(iii)" is any pair with $1\le L\le C_L(\ln\ln k)^{1/16}$ and planted root flow at least $\varepsilon_k$ at $\lambda^+$, for an arbitrary constant $C_L$ fixed before $k$; $n_0$ depends on $k$ (and $C_L$) only.
--
--   Differences from the source:
--   - generalization: (L, ϑ) as chosen in Theorem 4.8(iii) → every L ≥ 1 with L ≤ C_L (ln ln k)^{1/16} (any constant C_L) and every ϑ ∈ [0,1] whose planted root flow at λ⁺ is ≥ ε_k; reason: the pair of Theorem 4.8(iii) is such a pair (with C_L its O-constant), so this specializes to the source; the proof uses only these two properties
--   - encoding: B_L(Φ, v) and B_L(L_x, v) as formulas on their own variables → ballF on the same variable type, outside variables frozen by LocalUpdate; reason: the paper extends a ball update by keeping x unchanged outside the ball
--   - encoding: Φ_x: Pois(αn) clauses uniform among k-clauses satisfied by x → poisProb over clausesSatBy (fun _ : Fin 1 => x) with mean αn; reason: same law
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
--   - generalization: deterministic tree-update claims in the k-SAT setting → the deterministic clauses hold for arbitrary finite variable types and CNF clause widths, with any k in the window parameter; reason: the proof of reachability, reversibility and pruning uses only the tree structure and the marginal window; proper k-clause formulas are included verbatim
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 4.11 (with the definition of g_v), printed p. 29–30 (PDF 31–32)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_KSATSingleFlip_Connect_LocalUpdate

open scoped Classical BigOperators ENNReal
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 4.11 (comparison and concentration of local-update flow; printed pp. 29–30).
(i) For any formula `Φ`, `x ∈ Ω_Φ` and `v` with `B_L(Φ, v)` a tree, the flow at `v` of
LocalUpdate run on `B_L(Φ, v)` is at least `g_v(Φ, x)`, with equality when `v` is
`(L, k⁴)`-locally tree-structured in `L_x`.
(ii) For `Φ_x` made of `Pois(αn)` independent clauses uniform among the `k`-clauses satisfied by
`x`, with `λ⁺ = αk/(2^k − 1)` in the range of Theorem 4.8(iii) and `(L, ϑ)` as chosen there (any
`L ≥ 1`, `L = O((ln ln k)^{1/16})`, and `ϑ ∈ [0, 1]` with planted root flow at least `ε_k`), there
is an absolute `C > 0` such that `Pr(∑_v g_v(Φ_x, x) < ε_k n/2) ≤ 3 exp(−b_k n)` for
`b_k = exp(−C (L + 1) ln k)` and all `n ≥ n₀(k)`. -/
theorem lemma_4_11 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (Φ : GFormula V) (k L : ℕ) (ϑ : ℝ),
      1 ≤ L → 0 ≤ ϑ → ϑ ≤ 1 → ∀ x ∈ sols Φ, ∀ v : V, BallIsTree Φ v L →
        gFlow k L ϑ Φ x v ≤ luFlow (ballF Φ v L) v k L ϑ x v ∧
        (LocallyTree (Lx Φ x) v L (k ^ 4) →
          luFlow (ballF Φ v L) v k L ϑ x v = gFlow k L ϑ Φ x v)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ CL : ℝ, 0 < CL → ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0,
      ∀ α : ℝ, 0 ≤ α →
        α * k / ((2 : ℝ) ^ k - 1) ≤ Real.log k + Real.log (Real.log k) + gammaStar -
          1 / Real.rpow (Real.log (Real.log k)) (1 / 16) + 1 / Real.log k →
      ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ CL * Real.rpow (Real.log (Real.log k)) (1 / 16) →
      ∀ ϑ : ℝ, 0 ≤ ϑ → ϑ ≤ 1 →
        ENNReal.ofReal (epsK k) ≤ plantedFlow k (α * k / ((2 : ℝ) ^ k - 1)) L ϑ →
      ∀ x : Fin n → Bool,
        poisProb (clausesSatBy (k := k) (fun _ : Fin 1 => x)) (α * n)
            (fun Φ => ∑ v, gFlow k L ϑ (ofList Φ) x v < epsK k * n / 2) ≤
          3 * Real.exp (-(Real.exp (-C * (L + 1) * Real.log k)) * n)) := by sorry

end KSATSingleFlip.Connect
