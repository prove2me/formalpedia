-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cellTailAdmissibilityV1
-- name    : Kyprianou.Ch04.cellTailAdmissibilityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:40:51.84536+00:00
-- url     : https://prove2.me/theorems/2959e529-6592-5e93-b1a3-f36a9743d0a1
-- title:
--   Signed tail coefficient admissibility
-- statement:
--   Signed duplicate coefficients retain the endpoint measurability and energy hypotheses.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_finitePredictableTailBoxPhysicalIsometry
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem cellTailAdmissibilityV1 {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (s : Finset ι) (T : NNReal) (a b : ι → NNReal)
    (B : ι → Set ℝ) (H : ι → Ω → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) (hbT : ∀ i ∈ s, b i ≤ T)
    (hB : ∀ i ∈ s, MeasurableSet (B i))
    (hFa : ∀ i ∈ s, referenceIntensity ν (Ioc (a i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hFb : ∀ i ∈ s, referenceIntensity ν (Ioc (b i : ℝ) (T : ℝ) ×ˢ B i) ≠ ⊤)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (hH2 : ∀ i ∈ s, Integrable (fun ω => (H i ω)^2) P) :
    let U := s.product (Finset.univ : Finset Bool)
    let A (i : ι × Bool) := if i.2 then a i.1 else b i.1
    let C (i : ι × Bool) := B i.1
    let W (i : ι × Bool) (ω : Ω) := if i.2 then H i.1 ω else -H i.1 ω
    (∀ i ∈ U, A i ≤ T) ∧ (∀ i ∈ U, MeasurableSet (C i)) ∧
    (∀ i ∈ U, referenceIntensity ν (Ioc (A i : ℝ) (T : ℝ) ×ˢ C i) ≠ ⊤) ∧
    (∀ i ∈ U, StronglyMeasurable[F (A i)] (W i)) ∧
    (∀ i ∈ U, Integrable (fun ω => (W i ω)^2) P) := by
  sorry
end Kyprianou.Ch04
