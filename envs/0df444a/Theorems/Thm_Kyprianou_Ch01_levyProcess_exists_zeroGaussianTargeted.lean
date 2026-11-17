-- Prove2me | Theorems.Thm_Kyprianou_Ch01_levyProcess_exists_zeroGaussianTargeted
-- name    : Kyprianou.Ch01.levyProcess_exists_zeroGaussianTargeted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T12:47:22.006519+00:00
-- url     : https://prove2.me/theorems/c2f0896d-c8b6-45aa-bc96-93c18ff689c1
-- title:
--   Zero-Gaussian Lévy process existence with collision-safe triplet exponent imports
-- statement:
--   Theorem 1.6 restricted to admissible Lévy triples whose Gaussian variance is zero. Existence of a process with measurable marginals and characteristic exponent is already established in a public Prove2Me theorem ProbabilityTheory.exists_isLevyProcess_pureJump, proved in the completed LeanLevy fundamentals mission. This restricted case should follow by instantiating that theorem with drift T.drift and Lévy measure T.levyMeasure, using T.levyMeasure_isLevyMeasure and the Chapter 1 exponent definition. Its proof discharges a mathematically significant entire component of the unrestricted existence theorem. Source-equivalent reconstruction with a revised source definition whose Lean imports omit full Mathlib, removing a known transitive duplicate declaration with the proved pure-jump constructor.
-- source:
--   Kyprianou (2006), Chapter 1 Theorem 1.6, Lévy–Khintchine process construction, pure-jump case.

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.levyProcess_exists_zeroGaussianTargeted
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hzero : T.gaussianVariance = 0) :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (μ.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent T ξ) := by sorry
