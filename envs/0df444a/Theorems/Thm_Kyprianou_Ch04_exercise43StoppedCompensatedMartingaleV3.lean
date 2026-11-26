-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise43StoppedCompensatedMartingaleV3
-- name    : Kyprianou.Ch04.exercise43StoppedCompensatedMartingaleV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:48:32.195357+00:00
-- url     : https://prove2.me/theorems/6bd92e84-b241-4c2a-9523-c03d2a4cb5bb
-- title:
--   Exercise 4.3(ii): corrected stopped compensated martingale
-- statement:
--   The physical discounted compensated jump integral stopped at the original generator threshold is a true martingale, under explicit usual filtration conditions, local jump domination, exact predictable and Poisson regularity, and finite expected stopped absolute mass.
-- source:
--   Kyprianou (2006), Exercise 4.3(ii), pp. 106-107.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false


open Kyprianou.Ch04

/-- Exercise 4.3(ii), with explicit regularity and finite stopped absolute mass. -/
theorem Kyprianou.Ch04.exercise43StoppedCompensatedMartingaleV3
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (hAdapted : ∀ t : NNReal,
      Measurable[(F t)] (fun omega : Omega => X t omega))
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
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
    (Xleft : NNReal -> Omega -> Real)
          (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t →
            Tendsto (fun s : NNReal => X s omega)
              (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
          (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0}
            P triplet.levyMeasure)
          (hJumpLaw : ∀ᵐ omega : Omega ∂P,
            N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega)
    (hRC : F.IsRightContinuous)
    (hNull : ∀ (s : NNReal) (N A : Set Omega), MeasurableSet N → P N = 0 →
      A ⊆ N → MeasurableSet[F s] A)
    (hdom : ∀ y : ℝ, ∃ r : ℝ, 0 < r ∧ ∃ b : ℝ → ℝ,
      Integrable b triplet.levyMeasure ∧ ∀ z ∈ Set.Icc (y-r) (y+r),
        ∀ᵐ x ∂triplet.levyMeasure, ‖f (z+x)-f z‖ ≤ b x)
    (hLmeas : Measurable (fun z : ℝ × Omega => Xleft z.1.toNNReal z.2))
    (hLadapted : ∀ t : NNReal, Measurable[F t] (Xleft t))
    (hLpast : ∀ t : NNReal, Measurable[(F t).prod inferInstance]
      (fun z : Omega × ℝ => if z.2 ∈ Set.Icc (0 : ℝ) (t : ℝ)
        then Xleft z.2.toNNReal z.1 else 0))
    (hFuture : IsFutureIndependentPoissonMeasure P triplet.levyMeasure F N)
    (hPast : ∀ (t : NNReal) (B : Set (ℝ × ℝ)), MeasurableSet B →
      B ⊆ Set.Icc (0 : ℝ) (t : ℝ) ×ˢ Set.univ →
      Measurable[F t] (fun w => N.N w B))
    (hLocal : ∀ (t : NNReal) (j : ℕ) (w : Omega),
      N.N w (Set.Icc (0 : ℝ) (t : ℝ) ×ˢ spanningSets triplet.levyMeasure j) ≠ ⊤)
    (hFin : ∀ (n : ℕ) (t : NNReal),
      let tau : Omega → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
        ∃ u : NNReal, v = ↑u ∧
          (n : ℝ) < |∫ x, (f (X u w+x)-f (X u w)) ∂triplet.levyMeasure|}
      (∫⁻ w, ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ), ∫⁻ x,
        ENNReal.ofReal |if (s.toNNReal : WithTop NNReal) ≤ tau w then
          Real.exp (-lambda*s)*(f (Xleft s.toNNReal w+x)-f (Xleft s.toNNReal w))
          else 0| ∂triplet.levyMeasure ∂volume ∂P) < ⊤) :
          let M : NNReal -> Omega -> Real := fun t omega =>
            (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
              Real.exp (-lambda * z.1) *
                (f (Xleft (Real.toNNReal z.1) omega + z.2) -
                 f (Xleft (Real.toNNReal z.1) omega))
              ∂(N.N omega)) -
            (∫ s in Set.Icc (0 : Real) (t : Real),
              Real.exp (-lambda * s) *
                (∫ x : Real,
                  (f (X (Real.toNNReal s) omega + x) -
                   f (X (Real.toNNReal s) omega))
                  ∂triplet.levyMeasure) ∂volume)
          ∃ stop : Nat -> Omega -> NNReal -> NNReal,
            (∀ (n : Nat) (omega : Omega) (t : NNReal),
              let tau : WithTop NNReal :=
                sInf {v : WithTop NNReal |
                  ∃ s : NNReal, v = ↑s ∧
                    n < |∫ x : Real,
                      (f (X s omega + x) - f (X s omega))
                      ∂triplet.levyMeasure|}
              (stop n omega t : WithTop NNReal) =
                min (t : WithTop NNReal) tau) ∧
            ∀ n : Nat,
              MeasureTheory.Martingale
                (fun t omega => M (stop n omega t) omega) F P := by
  sorry
