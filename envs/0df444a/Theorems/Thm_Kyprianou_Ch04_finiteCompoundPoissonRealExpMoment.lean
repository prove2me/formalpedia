-- Prove2me | Theorems.Thm_Kyprianou_Ch04_finiteCompoundPoissonRealExpMoment
-- name    : Kyprianou.Ch04.finiteCompoundPoissonRealExpMoment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:47:27.641573+00:00
-- url     : https://prove2.me/theorems/1d6fdc29-4f6f-451b-a747-f0b40e589c20
-- title:
--   Finite compound Poisson law: exact real exponential moment
-- statement:
--   Convert the proved compound Poisson extended moment formula into integrability and an exact real integral at any exponent for which the mark exponential is integrable.
-- source:
--   Kyprianou (2006), Exercise 4.3(iv); unit marginal Lévy–Khintchine moment calculation.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.finiteCompoundPoissonRealExpMoment
    (nu : Measure Real) [IsFiniteMeasure nu] (beta : Real)
    (h : Integrable (fun x : Real => Real.exp (beta*x)) nu) :
    Integrable (fun x : Real => Real.exp (beta*x))
        (KSATSingleFlip.Connect.compoundPoisson nu) ∧
      (∫ x, Real.exp (beta*x) ∂(KSATSingleFlip.Connect.compoundPoisson nu)) =
        Real.exp (∫ x, (Real.exp (beta*x)-1) ∂nu) := by
  sorry
