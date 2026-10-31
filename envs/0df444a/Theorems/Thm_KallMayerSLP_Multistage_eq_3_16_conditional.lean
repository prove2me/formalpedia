-- Prove2me | Theorems.Thm_KallMayerSLP_Multistage_eq_3_16_conditional
-- name    : KallMayerSLP.Multistage.eq_3_16_conditional
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:19:29.995796+00:00
-- url     : https://prove2.me/theorems/eb53c4ab-67b2-4c61-b01a-f71c1e6d0e86
-- title:
--   (3.16) for conditional expectations
-- statement:
--   Let (3.10) satisfy Assumption 3.2 and let $n$ be a node of stage $t\ge2$ of a scenario tree. Then
--   $$
--   r_t\big(z_{t-1};\widehat\zeta_{t-1},\bar\xi^n_t\big)\le\mathbb E_{\xi_t}\big[r_t(z_{t-1};\widehat\zeta_{t-1},\xi_t)\mid\xi_t\in\Xi^t_n\big].
--   $$
--
--   This is Jensen's inequality on a single cell of the partition, the form in which (3.16) enters the proof of Lemma 3.1.
--
--   **Formalization Note** The inequality is multiplied by $\mathbb P_{\xi_t}(\Xi^t_n)$, so that it also makes sense on a null cell, where both sides are $0$.
--
--   Differences from the source:
--   - reading: Assumption 3.2: the A_tt complete fixed recourse matrices ∀t → complete recourse of A_tt for t = 2, …, T; reason: A_11 is not a recourse matrix, and the book's Example 3.1 calls a problem with a non-complete first stage complete fixed recourse; this is the weaker hypothesis, so the statement implies the ∀t one
--   - generalization: supp ℙ_{ξ_t} ⊆ Ξ^t → ξ_t ∈ Ξ^t almost surely; reason: the support inclusion implies the almost sure one, and they agree for closed Ξ^t, so the statement specializes to the source
--   - encoding: 𝔼[· | ξ_t ∈ Ξ^t_n], undefined on a null cell → multiplied out as the expectation under ℙ_{ξ_t} restricted to the cell; reason: the same quantity on a cell of positive probability, and 0 on a null cell
--   - encoding: z_{t-1} and ζ̂_t as finite sequences → full families z and w, of which only the coordinates the book lists are used; reason: the same functions; unused coordinates have no effect
--   - generalization: a partition of Ξ^{ν+1} into subintervals, |C_n| = r_n ≥ 1 → ScenarioTree, whose cells may be empty (a node may then have no child when Ξ^{ν+1} is empty); reason: every tree of p.261 is a ScenarioTree, so the statement specializes to the book's trees
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, p.264 (PDF 273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Assumption32
import Definitions.Def_KallMayerSLP_Multistage_rFn
import Definitions.Def_KallMayerSLP_Multistage_xiBar

namespace KallMayerSLP.Multistage

open MeasureTheory WassersteinDRO.Duality

/-- **Chapter 3, Jensen's inequality (3.16) for conditional expectations** (Kall & Mayer,
*Stochastic Linear Programming* (2005), Chapter 3, p.264, PDF 273):
`r_t(z_{t-1}; ζ̂_{t-1}, ξ̄^n_t) ≤ 𝔼_{ξ_t}[r_t(z_{t-1}; ζ̂_{t-1}, ξ_t) | ξ_t ∈ Ξ^t_n]` for a node `n` of
stage `t`.

**Formalization Note.** The inequality is multiplied out by `ℙ(ξ_t ∈ Ξ^t_n)`, with the right side
the expectation under `ℙ_{ξ_t}` restricted to `Ξ^t_n`, so that it also makes sense on a null cell,
where both sides are `0`. For a cell of positive probability it is the book's inequality. -/
theorem eq_3_16_conditional {D : MSLP} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ξ : ∀ t, Ω → Fin (D.r t) → ℝ} {Ξ : ∀ t, Set (Fin (D.r t) → ℝ)}
    (hA : Assumption32 D P ξ Ξ) (𝒯 : ScenarioTree D Ξ) {t : ℕ} (ht₂ : 2 ≤ t) (ht : t ≤ D.T)
    (n : 𝒯.Node t) (z : ∀ τ, Fin (D.n τ) → ℝ) (w : ∀ s, Fin (D.r s) → ℝ) :
    ((P.real (ξ t ⁻¹' 𝒯.cell t n) : ℝ) : EReal) *
        rFn D (fun t => P.map (ξ t)) t z (Function.update w t (xiBar 𝒯 P ξ t n)) ≤
      erealExpectation ((P.map (ξ t)).restrict (𝒯.cell t n)) fun v =>
        rFn D (fun t => P.map (ξ t)) t z (Function.update w t v) := by sorry

end KallMayerSLP.Multistage
