-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_4
-- name    : KSATSingleFlip.Connect.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:08:27.27251+00:00
-- url     : https://prove2.me/theorems/911e9874-6fc4-4c87-8209-7eb62c9a84cb
-- title:
--   Lemma 7.4 — correctness of Repair
-- statement:
--   For any $\Phi_0\subseteq\Phi^+$, $x\in\Omega_{\Phi_0}$ and $W\subseteq[n]$, $\mathrm{Repair}(\Phi^+,\Phi_0,x,W)$ returns an $(x,W)$-repair or Fail in $O_k(n(n+|\Phi^+|))$ time.
--
--   For sufficiently large $k$, fix $0\le m\le\frac{2^kn}{k}\big(\ln k+\ln\ln k+1+\frac{\ln\ln k+1/2}{\ln k}-\frac{6(\ln\ln k)^2}{(\ln k)^2}\big)$, $z\in\{0,1\}^n$ and an integer $t\ge0$; sample $M\sim\mathrm{Pois}(m)$, $\Phi^+\sim\Phi(k,n,M)$, and let $X$ be the state after $t$ Glauber steps on $\Phi_0 = \Phi^+[z]$ from $z$. With probability at least $1-e^{-\rho^8n}$, if $\Phi^+$ is regular and at most $\rho^4n$ clauses of $\Phi^+\setminus\Phi_0$ have at most one true literal under $X$, then $\mathrm{Repair}(\Phi^+,\Phi_0,X,W)$ returns a good $(X,W)$-repair for every $W\subseteq[n]$ with $|W|\le\rho^2n/2$.
--
--   In Lean the first part says: every run returns Fail or an $(x,W)$-repair, and every run (finished or not) costs at most $C_kn(n+|\Phi^+|)$ in the declared cost model `repairCost` $(i+2)(n+|\Phi^+|)$ for $i$ loop iterations — so in particular every run terminates.
--
--   Differences from the source:
--   - generalization: Repair with the fixed lexicographic choice rules of p. 60 → every run under every resolution of the choices (RStep); reason: the source's run is one of them; neither part of the proof uses a choice rule
--   - generalization: Reg with the paper's degree cutoff D_k → Reg with every cutoff D; reason: the proof (via Lemma 7.12) uses only LS(Φ⁺)
--   - encoding: O_k(n(n + |Φ⁺|)) time → ∃ C_k > 0 (after k): repairCost of every run and of every partial run ≤ C_k n (n + |Φ⁺|); reason: the paper gives no machine model; the cost model charges n + |Φ⁺| per pass exactly as the paper's own accounting (p. 62), and bounding partial runs states termination
--   - encoding: any k → k ≥ 1 in the first part; reason: a 0-clause (no literal) is not a k-SAT clause; it excludes only the degenerate width
--   - reading: no explicit range of n in the second part → ∃ n₀, ∀ n ≥ n₀; reason: standing convention of p. 2 (Lemma 7.11, which it uses, needs large n)
--   - encoding: m ≥ 0 (the Poisson mean) → m : ℝ, 0 ≤ m; reason: the Poisson mean need not be an integer
--   - encoding: M ∼ Pois(m) and then M independent clauses → poisExp/poisProb: the series ∑_M e^{-m} m^M/M! · (uniform average over M-tuples of clauses); reason: same law; the integrands lie in [0,1], so the series converges
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
--   - encoding: Repair returns a repair or Fail (and a good repair under the stated conditions) → existence of a completed RepairRun, together with the guarantee for every completed run; reason: the existential states completion explicitly; the universal alone only describes outputs conditional on a completed run
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.4, printed p. 54 (PDF 56)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_Glauber
import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.4 (correctness of Repair; printed p. 54).
Part 1: for any `Φ₀ ⊆ Φ⁺` (positions `I₀`), `x ∈ Ω_{Φ₀}` and `W ⊆ [n]`, every run of Repair
(Algorithm 3, under every resolution of its choices) returns an `(x, W)`-repair or `Fail`, and
every run, finished or not, has cost at most `C_k n (n + |Φ⁺|)` in the declared cost model
(`repairCost`), with `C_k` depending only on `k`.
Part 2: for sufficiently large `k`, `0 ≤ m ≤ (2^k n/k)(ln k + ln ln k + 1 + (ln ln k + 1/2)/ln k −
6(ln ln k)²/(ln k)²)`, fixed `z` and `t ≥ 0`, `M ∼ Pois(m)`, `Φ⁺ ∼ Φ(k, n, M)` and `X` the `t`-step
Glauber state on `Φ₀ = Φ⁺[z]` from `z`: with probability at least `1 − e^{−ρ^8 n}`, if `Φ⁺` is
regular and at most `ρ^4 n` clauses of `Φ⁺ ∖ Φ₀` have at most one true literal under `X`, then
Repair(Φ⁺, Φ₀, X, W) returns a good `(X, W)`-repair for every `W` with `|W| ≤ ρ² n/2`. The
statement is made for every value `D` of the degree cutoff in `Reg`. -/
theorem lemma_7_4 :
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (Φp : List (ProperClause n k))
      (I0 : Finset (Fin (ofList Φp).length)) (x : Fin n → Bool) (W : Finset (Fin n)),
      x ∈ sols (subF (ofList Φp) I0) →
        (∃ r i, RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i) ∧
        (∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
          RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i →
            (r = none ∨ ∃ U y, r = some (U, y) ∧ IsRepair (ofList Φp) x W U y) ∧
            (repairCost n Φp.length i : ℝ) ≤ C * n * (n + Φp.length)) ∧
        (∀ (s : RState (ofList Φp) x) (j : ℕ),
          RepairReach k (ofList Φp) I0 x (RState.init (ofList Φp) x W) s j →
            (repairCost n Φp.length j : ℝ) ≤ C * n * (n + Φp.length))) ∧
    (∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ m : ℝ, 0 ≤ m →
      m ≤ (2 : ℝ) ^ k * n / k * loosenessLambda k →
      ∀ (z : Fin n → Bool) (t D : ℕ),
        1 - Real.exp (-(rho k ^ 8) * n) ≤
          poisExp (allClauses n k) m (fun l =>
            uprob fun s : Fin t → Fin n × Bool =>
              let Φp := ofList l
              let I0 := satIdx Φp z
              let X := glauberState (subF Φp I0) z s
              Reg k D Φp → ((omittedWeak Φp I0 X).card : ℝ) ≤ rho k ^ 4 * n →
                ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
                  (∃ r i, RepairRun k Φp I0 X (RState.init Φp X W) r i) ∧
                  ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
                    RepairRun k Φp I0 X (RState.init Φp X W) r i →
                      ∃ U y, r = some (U, y) ∧ IsGoodRepair k Φp X W U y)) := by sorry

end KSATSingleFlip.Connect
