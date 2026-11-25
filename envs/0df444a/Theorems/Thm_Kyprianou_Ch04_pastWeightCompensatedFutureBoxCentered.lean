-- Prove2me | Theorems.Thm_Kyprianou_Ch04_pastWeightCompensatedFutureBoxCentered
-- name    : Kyprianou.Ch04.pastWeightCompensatedFutureBoxCentered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T19:08:31.98385+00:00
-- url     : https://prove2.me/theorems/b0a1c2ef-d852-44db-b444-071ef7f4c41f
-- title:
--   Zero mean of past weight times future compensated Poisson box
-- statement:
--   In Chapter 4 nonanticipating Poisson filtration, an F_u measurable integrable real-valued weight has vanishing expected product with the compensated count on a finite intensity measurable future time-space box. The product integrability is required explicitly, as is finite intensity. This is the cross-moment orthogonality step for compensated predictable jump integrals.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.4: predictable compensation and finite Poisson box orthogonality; same-space consequence of the proved Chapter 4 future box independence plus compensated centring.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_CompensatedIsometry
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Theorems.Thm_Kyprianou_Ch04_pastWeightIndependentFutureCompensatedBox
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An integrable past weight has zero centred cross moment with a future Poisson box. -/

theorem Kyprianou.Ch04.pastWeightCompensatedFutureBoxCentered
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (nu : Measure Real) [SigmaFinite nu]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (N : PoissonRandomMeasure.{0,0,0} P nu)
    (hFuture : Kyprianou.Ch04.IsFutureIndependentPoissonMeasure P nu F N)
    (u t : NNReal) (hut : u ≤ t)
    (B : Set Real) (hB : MeasurableSet B)
    (hFin : referenceIntensity nu (Set.Ioc (u : Real) (t : Real) ×ˢ B) ≠ ⊤)
    (f : Omega → Real)
    (hf : @StronglyMeasurable Omega Real _ (F u) f)
    (_hfi : Integrable f P)
    (_hprod : Integrable (fun omega =>
      f omega * N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega) P) :
    (∫ omega, f omega * N.compensated (Set.Ioc (u : Real) (t : Real) ×ˢ B) omega ∂P) = 0 := by
  sorry
