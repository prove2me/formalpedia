-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49GeneralExtendedRestrictedPathV6
-- name    : Kyprianou.Ch04.exercise49GeneralExtendedRestrictedPathV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:35:37.51188+00:00
-- url     : https://prove2.me/theorems/44a9e529-3808-457b-b8b3-21de10097d19
-- title:
--   exercise49GeneralExtendedRestrictedPathV6
-- statement:
--   exercise49GeneralExtendedRestrictedPathV6
-- source:
--   Exercise 4.9(iii): corrected ladder renewal proof

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49GeneralExtendedRestrictedPathV6
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hDet : ∀ (s : NNReal) (B : Set Ω), MeasurableSet[F s] B →
      Measure.map (fun w u => X (s+u) w-X s w) (P.restrict B) =
        P B • Measure.map (fun w u => X u w) P)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F τ)
    (a : Ω → NNReal) (ha : ∀ w, τ w ≠ ⊤ → τ w = (a w : WithTop NNReal)) :
    AEMeasurable (fun w u => X (a w + u) w - X (a w) w) (P.restrict {w | τ w ≠ ⊤}) ∧
    ∀ B : Set Ω, (∀ s : NNReal, MeasurableSet[F s] (B ∩ {w | τ w ≤ (s : WithTop NNReal)})) →
      Measure.map (fun w u => X (a w + u) w - X (a w) w)
        (P.restrict (B ∩ {w | τ w ≠ ⊤})) =
      P (B ∩ {w | τ w ≠ ⊤}) • Measure.map (fun w u => X u w) P := by
  sorry
