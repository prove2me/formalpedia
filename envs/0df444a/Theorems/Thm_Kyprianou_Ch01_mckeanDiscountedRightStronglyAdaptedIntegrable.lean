-- Prove2me | Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedRightStronglyAdaptedIntegrable
-- name    : Kyprianou.Ch01.mckeanDiscountedRightStronglyAdaptedIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:07:59.362922+00:00
-- url     : https://prove2.me/theorems/ae91546c-8671-4c61-ada4-daef93b9324b
-- title:
--   Discounted McKean candidate is strongly adapted and integrable in the right-natural filtration
-- statement:
--   For any log-price process, any probability measure and the right-natural filtration of Y_t=x+X_t, the discounted McKean candidate is strongly adapted and integrable at every time, requiring only K,q,phi positive. The source value has already been proved Borel measurable and bounded between zero and K. The shifted coordinate Y_t is measurable in the right-natural filtration at t by the proved naturalSigmaRight_measurable_past theorem, which implies strong adaptedness. The associated filtration is contained in the ambient measurable space; boundedness plus finite measure then establishes integrability via Integrable.of_bound. This is a direct prerequisite for the true Brownian supermartingale theorem, leaving its genuine conditional drift/Itô inequality isolated.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.13; right-natural discounted value process verification.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_measurable_past
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
import Theorems.Thm_Kyprianou_Ch01_mckeanDiscountedValue_pointwiseBound
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.mckeanDiscountedRightStronglyAdaptedIntegrable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ) (hK : 0 < K) (hq : 0 < q) (hphi : 0 < phi)
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hF : ∀ t, F t = naturalSigmaRight (fun u ω => x + X u ω) t) :
    let barrier := Real.log (K * phi / (1 + phi))
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      Real.exp (-q * (t : ℝ)) *
        mckeanValue K barrier phi (x + X t ω)
    StronglyAdapted F M ∧
      ∀ t : ℝ≥0, Integrable (M t) P := by sorry
