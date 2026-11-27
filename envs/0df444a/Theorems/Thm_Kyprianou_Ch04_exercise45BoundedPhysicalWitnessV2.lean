-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45BoundedPhysicalWitnessV2
-- name    : Kyprianou.Ch04.exercise45BoundedPhysicalWitnessV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T23:30:22.764293+00:00
-- url     : https://prove2.me/theorems/7faf9809-fa67-4fa7-91f8-e70b3fafec1a
-- title:
--   Original-space bounded pure-jump stochastic integral and Ito witness
-- statement:
--   On the original pure-jump Levy probability space, every bounded smooth test jet has a right-continuous martingale and physical drift/large-jump stochastic integral satisfying UCP and the Ito formula. No supplied cutoff approximation is assumed.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45BoundedPhysicalWitnessV2 :
∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hNoGaussian : triplet.gaussianVariance = 0)
    (hTriplet : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hFiltration : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    (N : PoissonRandomMeasure.{0,0,0}
      P triplet.levyMeasure)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hLeftZero : ∀ᵐ w ∂P, Xleft 0 w = X 0 w)
    (hNLaw : ∀ᵐ omega : Omega ∂P,
      N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega)
    (f fTime fSpace fSpace2 : Real -> Real -> Real)
    (hTime : ∀ s x : Real,
      fTime s x = deriv (fun u : Real => f u x) s)
    (hSpace : ∀ s x : Real,
      fSpace s x = deriv (fun u : Real => f s u) x)
    (hSpace2 : ∀ s x : Real,
      fSpace2 s x = deriv (fun u : Real => fSpace s u) x)
    (hSmoothTime : ∀ x : Real, ContDiff Real 1 (fun s => f s x))
    (hSmoothSpace : ∀ s : Real, ContDiff Real 2 (fun x => f s x))
    (hJoint : ContinuousOn (fun z : Real × Real => f z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fTime z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ) ∧
      ContinuousOn (fun z : Real × Real => fSpace2 z.1 z.2)
        (Set.Ici (0 : Real) ×ˢ Set.univ))
    (X2 : NNReal -> Omega -> Real)
    (hX2Representation : ∀ t omega,
      X2 t omega =
        triplet.drift * (t : Real) +
        ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
          {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega))
    (K : Real) (hK : 0 < K)
    (hBound : ∀ s x : Real, 0 ≤ s →
      |f s x| ≤ K ∧ |fTime s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K),
    let D : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
    let R : NNReal → Omega → Real := fun t omega =>
      f (t : Real) (X t omega) - (
              f 0 (X 0 omega) +
              (∫ s in Set.Icc (0 : Real) (t : Real),
                fTime s (X (Real.toNNReal s) omega) ∂volume) +
              (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
                (f z.1 (Xleft (Real.toNNReal z.1) omega + z.2) -
                 f z.1 (Xleft (Real.toNNReal z.1) omega) -
                 z.2 * fSpace z.1 (Xleft (Real.toNNReal z.1) omega))
                ∂(N.N omega)))
    ∃ M : NNReal → Omega → Real,
      Martingale M F P ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun u => M u w) (Ici t) t) ∧
      IsStochasticIntegralInProbabilityV2 P X
        (fun t w => fSpace (t : ℝ) (Xleft t w)) (fun t w => D t w + M t w) ∧
      (∀ᵐ w ∂P, ∀ t, R t w = D t w + M t w)
 := by
  sorry
end Kyprianou.Ch04
