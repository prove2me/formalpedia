-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteSimpleCharToRawKLSV1
-- name    : Kyprianou.Ch02.prmFiniteSimpleCharToRawKLSV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T18:34:47.189602+00:00
-- url     : https://prove2.me/theorems/01da34d4-3a47-4d17-b697-e4095095f774
-- title:
--   Pass finite-simple marked Poisson characteristic exponents to the raw signed mark
-- statement:
--   Assuming the exact characteristic exponent identity holds for all real simple marks, approximate identity x by StronglyMeasurable.approx simple functions (pointwise all x). Proved prmSimpleMarkFiniteWindowIntegralAETendstoV1 gives almost sure convergence of the finite-activity signed integral. Apply complex dominated convergence to e^{iξX_n}, bounded by 1, and the ν-integral integrands exp(iξf_n(x))-1, bounded by 2 on finite ν(B). Preserve the zero-intensity case and avoid finite first moment assumptions.
-- source:
--   Kyprianou (2006) Ch.2 Eq.2.3, finite-activity Lévy–Khintchine.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteSimpleCharToRawKLSV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hSimple : ∀ (f : SimpleFunc ℝ ℝ) (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), f z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * f x : ℝ) : ℂ))) - 1) ∂ν)) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by sorry
