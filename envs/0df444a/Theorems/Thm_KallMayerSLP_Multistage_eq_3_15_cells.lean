-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_15_cells
-- name    : KallMayerSLP.Multistage.eq_3_15_cells
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:19:32.205184+00:00
-- url     : https://prove2.me/theorems/3859ac00-1db1-4412-b9b0-316aede3145c
-- title:
--   (3.15), last line — $\Phi_t$ splits along the partition of $\Xi^t$
-- statement:
--   Let (3.10) satisfy Assumption 3.2 and let $h$ be a node of a stage $t<T$ of a scenario tree. Then
--   $$
--   \Phi_{t+1}(z_t;\widehat\zeta_t)=\sum_{\nu\in C_h}\mathbb P_{\xi_{t+1}}\big(\Xi^{t+1}_\nu\big)\,\mathbb E_{\xi_{t+1}}\big[r_{t+1}(z_t;\widehat\zeta_t,\xi_{t+1})\mid\xi_{t+1}\in\Xi^{t+1}_\nu\big].
--   $$
--
--   This is the last line of (3.15), which compares $\Phi$ with the aggregated recursion cell by cell.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: 𝔼[· | ξ_t ∈ Ξ^t_n], undefined on a null cell → multiplied out as the expectation under ℙ_{ξ_t} restricted to the cell; reason: the same quantity on a cell of positive probability, and 0 on a null cell
--   - encoding: z_{t-1} and ζ̂_t as finite sequences → full families z and w, of which only the coordinates the book lists are used; reason: the same functions; unused coordinates have no effect
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.15), p.263 (PDF 272)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree
import Definitions.Def_KallMayerSLP_Multistage_rFn

namespace KallMayerSLP.Multistage

open MeasureTheory WassersteinDRO.Duality

/-- **Chapter 3, (3.15), last line** (Kall & Mayer, *Stochastic Linear Programming* (2005),
Chapter 3, (3.15), p.263, PDF 272): the expectation defining `Φ_{t+1}` splits along the cells of
the children of a node `h` of stage `t`,
`Φ_{t+1}(z_t; ζ̂_t) = Σ_{ν∈C_h} ℙ_{ξ_{t+1}}(Ξ^{t+1}_ν) 𝔼_{ξ_{t+1}}[r_{t+1}(z_t; ζ̂_t, ξ_{t+1}) | ξ_{t+1} ∈ Ξ^{t+1}_ν]`.

**Formalization Note.** Each term `ℙ(Ξ_ν) 𝔼[· | Ξ_ν]` is multiplied out as the expectation under
`ℙ_{ξ_{t+1}}` restricted to `Ξ_ν`, so a null cell contributes `0` and no conditional expectation
given a null event appears. -/
theorem eq_3_15_cells {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ) {t : ℕ} (ht₁ : 1 ≤ t) (ht : t < D.T)
    (h : 𝒯.Node t) (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ) :
    open Classical in
    Phi D (fun t => P.map (ξ t)) (t + 1) z w =
      ∑ ν : {ν : 𝒯.Node (t + 1) // 𝒯.parent t ν = h},
        erealExpectation ((P.map (ξ (t + 1))).restrict (𝒯.cell (t + 1) ν)) fun v =>
          rFn D (fun t => P.map (ξ t)) (t + 1) z (Function.update w (t + 1) v) := by sorry

end KallMayerSLP.Multistage
