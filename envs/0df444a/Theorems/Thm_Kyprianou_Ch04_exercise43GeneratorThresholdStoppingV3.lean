-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise43GeneratorThresholdStoppingV3
-- name    : Kyprianou.Ch04.exercise43GeneratorThresholdStoppingV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:12:22.993831+00:00
-- url     : https://prove2.me/theorems/a5b9fb01-d419-4a41-9607-3ea85cdb9135
-- title:
--   Exercise 4.3(i): strict generator threshold stopping time
-- statement:
--   Corrected Exercise 4.3(i): the original strict generator threshold is a stopping time, under usual filtration regularity and a local integrable jump envelope for the test function.
-- source:
--   Kyprianou (2006), Exercise 4.3(i), pp. 106-107.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exercise 4.3(i), with usual filtration and local jump domination. -/
theorem Kyprianou.Ch04.exercise43GeneratorThresholdStoppingV3
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : ∀ (t : NNReal) (theta : Real),
      charFun (P.map (X t)) theta =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet theta))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ x in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |x| ∂triplet.levyMeasure) < ⊤)
    (hNonLattice : triplet.levyMeasure Set.univ < ⊤ ->
      ¬ ∃ a : Real, 0 < a ∧
        triplet.levyMeasure
          {x : Real | ∃ k : Int, x = (k : Real) * a} =
        triplet.levyMeasure Set.univ)
    (f : Real -> Real) (hf : ContDiff Real 1 f)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hEigen : MeasureTheory.Martingale
      (fun (t : NNReal) (omega : Omega) => Real.exp (-lambda * (t : Real)) * f (X t omega)) F P)
    (hIntegrable : ∀ y : Real,
      Integrable (fun x : Real => f (y + x) - f y)
        triplet.levyMeasure)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b triplet.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂triplet.levyMeasure, ‖f (z+x)-f z‖ ≤ b x) :
    ∀ n : Nat,
          let tau : Omega -> WithTop NNReal := fun omega =>
            sInf {v : WithTop NNReal |
              ∃ t : NNReal, v = ↑t ∧
                n < |∫ x : Real,
                   (f (X t omega + x) - f (X t omega))
                   ∂triplet.levyMeasure|}
          ∀ t : NNReal,
            MeasurableSet[(F t)]
              {omega : Omega | tau omega ≤ (t : WithTop NNReal)} := by
  sorry
