-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_lemma_7_12
-- name    : KSATSingleFlip.Connect.lemma_7_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:08:22.974024+00:00
-- url     : https://prove2.me/theorems/cb737f60-fa2f-4139-8e41-f2e374fb1186
-- title:
--   Lemma 7.12 — Repair returns a good repair under regularity and the bounds of Lemma 7.11
-- statement:
--   Let $k$ and $n\ge n_0(k)$ be sufficiently large, fix $\Phi_0\subseteq\Phi^+$ and $x\in\Omega_{\Phi_0}$, and put $D = \{C\in\Phi^+\setminus\Phi_0 : |\mathrm{sat}_x(C)|\le1\}$. Suppose $\Phi^+$ is regular, $|D|\le\rho^4n$, and the three bounds of Lemma 7.11 hold for $(\Phi^+,\Phi_0,x)$. Then $\mathrm{Repair}(\Phi^+,\Phi_0,x,W)$ returns a good $(x,W)$-repair ($|U|\le|W|/(2\rho)+\rho^2n/8$) for every $W\subseteq[n]$ with $|W|\le\rho^2n/2$.
--
--   In Lean: every run of Algorithm 3, under every resolution of its choices, returns some $(U,y)$ that is a good $(x,W)$-repair.
--
--   Differences from the source:
--   - generalization: Repair with the fixed lexicographic choice rules of p. 60 (pending clause, tree, shortest augmenting paths) → every run of RStep under every resolution of the choices (Augment: any pair matching on J ∪ {C} keeping all matched variables matched); reason: the source's deterministic run is one of these runs, so the statement specializes to the source; the proof uses no choice rule
--   - generalization: Reg with the paper's degree cutoff D_k → Reg with every cutoff D; reason: the proof uses only LS(Φ⁺); LT is never used, so the source's D_k is a special case
--   - encoding: Φ₀ ⊆ Φ⁺ → a set I₀ of positions of the clause list Φ⁺; reason: sub-multisets of an indexed collection
--   - encoding: variables [n] = {1,…,n}, formulas as indexed clause collections → variables Fin n; Φ(k,n,m) = uniform law on the published Formula n k m; other formulas are clause lists (position = clause index), sub-formulas are sets of positions; reason: bijective reindexing; repeated clauses stay distinct, as in the paper's indexed collections
--   - encoding: Repair returns a repair or Fail (and a good repair under the stated conditions) → existence of a completed RepairRun, together with the guarantee for every completed run; reason: the existential states completion explicitly; the universal alone only describes outputs conditional on a completed run
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Lemma 7.12, printed p. 64 (PDF 66)

import Mathlib
import Definitions.Def_SATComputability
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators
open OAI.FixedClauseThreshold

namespace KSATSingleFlip.Connect

/-- Lemma 7.12 (printed p. 64). For sufficiently large `k` and `n ≥ n₀(k)`: fix `Φ₀ ⊆ Φ⁺`
(positions `I₀`) and `x ∈ Ω_{Φ₀}`, put `D = {C ∈ Φ⁺ ∖ Φ₀ : |sat_x(C)| ≤ 1}`. If `Φ⁺` is regular,
`|D| ≤ ρ^4 n` and the three bounds of Lemma 7.11 hold for `(Φ⁺, Φ₀, x)`, then for every
`W ⊆ [n]` with `|W| ≤ ρ² n/2`, Repair(Φ⁺, Φ₀, x, W) returns a good `(x, W)`-repair: every run of
Algorithm 3 (under every resolution of its choices) returns a good repair. The statement is made
for every value `D` of the degree cutoff in `Reg`. -/
theorem lemma_7_12 :
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (D : ℕ) (Φp : List (ProperClause n k))
      (I0 : Finset (Fin (ofList Φp).length)) (x : Fin n → Bool),
      x ∈ sols (subF (ofList Φp) I0) → Reg k D (ofList Φp) →
      ((omittedWeak (ofList Φp) I0 x).card : ℝ) ≤ rho k ^ 4 * n →
      RepairBounds k (ofList Φp) I0 x →
      ∀ W : Finset (Fin n), (W.card : ℝ) ≤ rho k ^ 2 * n / 2 →
        (∃ r i, RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i) ∧
        ∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
          RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i →
            ∃ U y, r = some (U, y) ∧ IsGoodRepair k (ofList Φp) x W U y := by sorry

end KSATSingleFlip.Connect
