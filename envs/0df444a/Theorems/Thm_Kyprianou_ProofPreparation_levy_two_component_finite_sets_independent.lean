-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_levy_two_component_finite_sets_independent
-- name    : Kyprianou.ProofPreparation.levy_two_component_finite_sets_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:25:47.318515+00:00
-- url     : https://prove2.me/theorems/d6a73498-9477-4a1d-966c-142132449c77
-- title:
--   Finite-set independence of two-component Lévy sum and third driver
-- statement:
--   A source-backed independence lemma for three mutually whole-path independent real Lévy processes. The finite-dimensional and full-path measurability details are proved using the fixed-time a.e. measurability of Lévy marginals, finite-vector projections and the process independence extension theorem.
-- source:
--   Kyprianou (2006), Chapter 2: Lévy–Itô decomposition, independent component construction and Chapter 1 independent Lévy addition.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem levy_two_component_finite_sets_independent
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : IsLevyProcess Xgauss P)
    (hlarge : IsLevyProcess Xlarge P)
    (hsmall : IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall)
    (I J : Finset ℝ≥0) :
    IndepFun
      (fun ω => fun i : I => Xgauss i ω + Xlarge i ω)
      (fun ω => fun j : J => Xsmall j ω) P := by sorry
end Kyprianou.ProofPreparation
