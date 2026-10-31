-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_lemma_3_1
-- name    : KallMayerSLP.Multistage.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:20:53.754816+00:00
-- url     : https://prove2.me/theorems/fdd53734-5b0c-4fa9-b74d-22dccf840577
-- title:
--   Lemma 3.1 — the aggregated problem (3.14) gives a lower bound on (3.10)
-- statement:
--   Let problem (3.10) satisfy Assumption 3.2: only the right-hand sides are random and affine in $\zeta_t$, the $\xi_t$ are bounded within intervals $\Xi^t$ and stochastically independent, and the $A_{tt}$ are complete fixed recourse matrices. Then for any subfiltration $\widehat{\mathcal F}$ constructed as on p.261, that is, for any scenario tree with its partitions of the $\Xi^t$, the optimal value of the aggregated problem
--   $$
--   \min\sum_{m\in\mathcal N}p_mc_{t_m}^{\mathsf T}x_m\quad\text{s.t.}\quad\sum_{m\in\mathcal H(n)}A_{t_nt_m}x_m=b_{t_n}(\widehat\zeta^n)\ \ \forall n\in\mathcal N,\quad x_m\ge0\ \ \forall m\in\mathcal N
--   $$
--   is a lower bound of the optimum in (3.10).
--
--   This is the multistage counterpart of the Jensen lower bound of two-stage programs: replacing the distribution by the conditional means on the cells of any partition tree turns a problem over decision functions into a finite linear program with no larger value. Example 3.1 shows that the conclusion fails without independence.
--
--   **Formalization Note** The distributions are arbitrary, subject to Assumption 3.2; there is no finiteness restriction. Both optimal values are infima in the extended reals, so infeasible and unbounded problems are covered.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: subfiltration ℱ̂ constructed as on p.261 → a ScenarioTree; reason: the tree with its partitions is the data of that construction
--   - encoding: stage 1 written apart from stages 2, …, T → one formula for t = 1, …, T, with the one-point state space Hist r 1; reason: the same constraints and objective; x_1 and b_1 are deterministic
--   - encoding: min → infimum in EReal; reason: +∞ on infeasible and -∞ on unbounded problems; the book assumes neither case away
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
--   - encoding: ξ̄^n_t = 𝔼[ξ_t | ξ_t ∈ Ξ^t_n], undefined on a P-null cell → xiBar = 0 on a P-null cell (Lean's 0⁻¹ = 0); reason: such a node and its descendants have p_n = 0, and their constraints are solvable by complete recourse of A_tt (t ≥ 2), so no value of (3.14) depends on the choice
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Lemma 3.1, p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_value
import Definitions.Def_KallMayerSLP_Multistage_aggValue

namespace KallMayerSLP.Multistage

open MeasureTheory

/-- **Chapter 3, Lemma 3.1** (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3,
Lemma 3.1, p.263, PDF 272): "Let problem (3.10) satisfy Assumption 3.2. Then for any subfiltration
`ℱ̂` constructed as above, the optimal value of the aggregated problem (3.14) is a lower bound of the
optimum in (3.10)."

**Formalization Note.** A subfiltration constructed as on p.261 is a `ScenarioTree`. The
distributions are arbitrary, subject to Assumption 3.2. Both optimal values are infima in `EReal`
(see `value`, `aggValue`), so the statement also covers infeasible and unbounded problems. -/
theorem lemma_3_1 {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ) :
    aggValue 𝒯 P ξ ≤ value D P ξ := by sorry

end KallMayerSLP.Multistage
