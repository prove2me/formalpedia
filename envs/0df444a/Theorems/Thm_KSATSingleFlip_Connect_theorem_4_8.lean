-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_theorem_4_8
-- name    : KSATSingleFlip.Connect.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:08:31.682379+00:00
-- url     : https://prove2.me/theorems/c151e6b7-6aa3-4862-9dca-1149f6a89d4f
-- title:
--   Theorem 4.8 — local update on a tree: reachability, reversibility, clause pruning, planted root flow $\ge\varepsilon_k$
-- statement:
--   For any integer $L\ge1$, tree formula $\Phi$ rooted at $o$ with depth at most $L$, retention probability $\vartheta\in[0,1]$ and $x\in\Omega_\Phi$, let $y\leftarrow\mathrm{LocalUpdate}(x)$ (Algorithm 1).
--
--   (i) It always holds that $\Delta(x,y)$ contains no variable of depth $L$, and $x$ and $y$ are joined by a path of length $d_H(x,y)$ in $G_1(\Phi)$; moreover $\Pr(\mathrm{LocalUpdate}(x') = y') = \Pr(\mathrm{LocalUpdate}(y') = x')$ for all $x',y'\in\Omega_\Phi$.
--
--   (ii) The law of $\Delta(x,y)$ is unchanged when $\Phi$ is replaced by $B_L(L_x,o)$, keeping $L,\vartheta$ fixed.
--
--   (iii) For sufficiently large $k$ and every $0\le\lambda^+\le\ln k+\ln\ln k+\gamma^*-(\ln\ln k)^{-1/16}+1/\ln k$ there exist $L = O((\ln\ln k)^{1/16})$ and $\vartheta\in[0,1]$ such that for $(\Phi,x)$ sampled to depth $L$ from $\mathrm{Tree}_{\mathrm{pl}}(\lambda^+)$,
--   $$\mathbb E\Big[\frac{\mathbf 1\{y_o\ne x_o\}}{\max\{1,d_H(x,y)\}}\Big]\ \ge\ \varepsilon_k := \frac{(\ln k)^{10}}{k}.$$
--   Parts (i)–(ii) are stated for every finite variable type and every clause width $k$ (which enters Algorithm 1 only through $a_k$); a path in $G_1(\Phi)$ is a satisfying path.
--
--   Differences from the source:
--   - encoding: "it always holds" for y ← LocalUpdate(x) → for every y with Pr(LocalUpdate(x) = y) > 0; reason: the possible outputs over all coin values are exactly the y of positive probability
--   - encoding: B_L(L_x, o) as a formula on its own variables → ballF (Lx Φ x) o L on the same variable type; LocalUpdate freezes variables not connected to the root; reason: the variables outside the ball carry no clause and are kept at x, which is how the paper extends a ball update (§4.3); the law of ∆ is the same
--   - encoding: L = O((ln ln k)^{1/16}) → ∃ absolute C > 0 with 1 ≤ L ≤ C (ln ln k)^{1/16}; reason: O-constant made explicit; it is fixed before k
--   - encoding: E over (Φ, x) from Tree_pl(λ⁺) and the coins → plantedFlow: the [0,∞]-valued sum over signed trees of their probability times the flow; reason: the flow lies in [0,1], so this is the expectation
--   - generalization: deterministic tree-update claims in the k-SAT setting → the deterministic clauses hold for arbitrary finite variable types and CNF clause widths, with any k in the window parameter; reason: the proof of reachability, reversibility and pruning uses only the tree structure and the marginal window; proper k-clause formulas are included verbatim
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Theorem 4.8, printed p. 25 (PDF 27)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_KSATSingleFlip_Connect_LocalUpdate

open scoped Classical BigOperators ENNReal

namespace KSATSingleFlip.Connect

/-- Theorem 4.8 (local update on a tree; printed p. 25). For every integer `L ≥ 1`, tree formula
`Φ` rooted at `o` with depth at most `L`, `ϑ ∈ [0, 1]` and `x ∈ Ω_Φ`, with `y ← LocalUpdate(x)`
(Algorithm 1; `k` is the clause width entering `a_k`):
(i) every possible output `y` changes no depth-`L` variable and is joined to `x` by a path of
length `d_H(x, y)` in `G_1(Φ)`, and `Pr(LocalUpdate(x′) = y′) = Pr(LocalUpdate(y′) = x′)` for all
`x′, y′ ∈ Ω_Φ`; (ii) the law of `∆(x, y)` is unchanged when `Φ` is replaced by `B_L(L_x, o)`;
(iii) for sufficiently large `k` and every `0 ≤ λ⁺ ≤ ln k + ln ln k + γ* − (ln ln k)^{−1/16} +
1/ln k` there are `L = O((ln ln k)^{1/16})` and `ϑ ∈ [0, 1]` whose planted root flow on
`Tree_pl(λ⁺)` truncated at depth `L` is at least `ε_k = (ln k)^{10}/k`. -/
theorem theorem_4_8 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (Φ : GFormula V) (o : V) (k L : ℕ) (ϑ : ℝ),
      1 ≤ L → IsTreeFormula Φ o L → 0 ≤ ϑ → ϑ ≤ 1 →
        (∀ x ∈ sols Φ, ∀ y : V → Bool, 0 < luProb Φ o k L ϑ x y →
          (∀ v ∈ disagree x y, vdepth Φ o v ≠ L) ∧
          ∃ p, IsSatPath Φ p x y ∧ pathLength p = hamming x y) ∧
        (∀ x ∈ sols Φ, ∀ y ∈ sols Φ, luProb Φ o k L ϑ x y = luProb Φ o k L ϑ y x) ∧
        (∀ x ∈ sols Φ, ∀ S : Finset V,
          ∑ y ∈ Finset.univ.filter (fun y => disagree x y = S), luProb Φ o k L ϑ x y =
            ∑ y ∈ Finset.univ.filter (fun y => disagree x y = S),
              luProb (ballF (Lx Φ x) o L) o k L ϑ x y)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ k0 : ℕ, ∀ k ≥ k0, ∀ lamp : ℝ, 0 ≤ lamp →
      lamp ≤ Real.log k + Real.log (Real.log k) + gammaStar -
        1 / Real.rpow (Real.log (Real.log k)) (1 / 16) + 1 / Real.log k →
      ∃ L : ℕ, 1 ≤ L ∧ (L : ℝ) ≤ C * Real.rpow (Real.log (Real.log k)) (1 / 16) ∧
        ∃ ϑ : ℝ, 0 ≤ ϑ ∧ ϑ ≤ 1 ∧ ENNReal.ofReal (epsK k) ≤ plantedFlow k lamp L ϑ) := by sorry

end KSATSingleFlip.Connect
