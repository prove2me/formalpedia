-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45BoundedWitnessFromSuppliedCutoffsV1
-- name    : Kyprianou.Ch04.exercise45BoundedWitnessFromSuppliedCutoffsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-27T00:12:07.959794+00:00
-- url     : https://prove2.me/theorems/9d3cb55e-1620-5c99-8663-1c6377ffa96f
-- title:
--   Bounded physical witness from supplied pure-jump cutoffs
-- statement:
--   The existing bounded pure-jump Ito limit, together with the supplied-cutoff martingale result and terminal L1 convergence, gives a right-continuous physical martingale witness.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)-(iv).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45BoundedWitnessFromSuppliedCutoffsV1 :
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
    (K : Real) (hK : 0 < K)
    (hBound : ∀ s x : Real, 0 ≤ s ->
      |f s x| ≤ K ∧ |fTime s x| ≤ K ∧
      |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K)
    (Xeps : Real -> NNReal -> Omega -> Real)
    (XepsLeft : Real -> NNReal -> Omega -> Real)
    (X2 : NNReal -> Omega -> Real)
    (hXepsInitial : ∀ epsilon omega, 0 < epsilon -> epsilon < 1 ->
      Xeps epsilon 0 omega = X 0 omega)
    (hXepsLeft : ∀ epsilon : Real, 0 < epsilon -> epsilon < 1 ->
      ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
        Tendsto (fun s : NNReal => Xeps epsilon s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (XepsLeft epsilon t omega)))
    (hX2Representation : ∀ t omega,
      X2 t omega =
        triplet.drift * (t : Real) +
        ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
                   {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega))
    (hXepsRepresentation : ∀ (epsilon : Real),
      0 < epsilon -> epsilon < 1 -> ∀ t omega,
      Xeps epsilon t omega = X2 t omega +
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
             {x : Real | epsilon < |x| ∧ |x| < 1},
          z.2 ∂(N.N omega)) -
        (t : Real) * (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
          x ∂triplet.levyMeasure))
    (Mε : Real -> NNReal -> Omega -> Real)
    (hMRepresentation : ∀ (epsilon : Real),
      0 < epsilon -> epsilon < 1 -> ∀ t omega,
      Mε epsilon t omega =
        (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
            {x : Real | epsilon < |x| ∧ |x| < 1},
          z.2 * fSpace z.1 (XepsLeft epsilon (Real.toNNReal z.1) omega)
            ∂(N.N omega)) -
        (∫ s in Set.Icc (0 : Real) (t : Real),
          (∫ x in {x : Real | epsilon < |x| ∧ |x| < 1},
            x * fSpace s (XepsLeft epsilon (Real.toNNReal s) omega)
            ∂triplet.levyMeasure) ∂volume))
    (hConvergence : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
          Tendsto (fun epsilon : Real => Xeps epsilon t omega)
            (nhdsWithin (0 : Real) (Set.Ioi 0))
            (nhds (X t omega))),
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
