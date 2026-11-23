-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionJointIncrementProductLawV2
-- name    : Kyprianou.Ch02.prmFiniteRegionJointIncrementProductLawV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T11:19:35.505385+00:00
-- url     : https://prove2.me/theorems/be58dba0-7845-4659-ac70-94bd96e4d55f
-- title:
--   Poisson finite-region JointIncrementProductLaw
-- statement:
--   Finite-dimensional product law for disjoint marked-increment integrals, assuming X is the exact original Poisson integral. Use the KLS PRM independent_disjoint sigma-field property, measurable marked-strip integral and strip-additivity. The already Proved Chapter 1 theorem converts this law and coordinate measurability into HasIndependentIncrements. This v2 source interface corrects the placement of the parameter X and its exact-equality hypothesis before the theorem conclusion.
-- source:
--   Kyprianou (2006) Chapter 2, finite-activity marked PRM integral; exact Open source-facing increment targets 61da0440 and 84c870a3; reuse proved Ch01 and Ch06 bridges.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionJointIncrementProductLawV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (X : ℝ≥0 → Ω → ℝ) (hX : X = (fun (q : ℝ≥0) (ω : Ω) =>
      ∫ z in (Set.Ioc (0 : ℝ) (q : ℝ) ×ˢ B), z.2 ∂(N.N ω))) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0), Monotone t →
      P.map (fun (ω : Ω) (k : Fin n) =>
        ProbabilityTheory.increment X (t k.castSucc) (t k.succ) ω) =
      Measure.pi (fun k : Fin n =>
        P.map (ProbabilityTheory.increment X (t k.castSucc) (t k.succ))) := by sorry
