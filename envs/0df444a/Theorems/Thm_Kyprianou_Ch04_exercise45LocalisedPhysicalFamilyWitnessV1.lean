-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedPhysicalFamilyWitnessV1
-- name    : Kyprianou.Ch04.exercise45LocalisedPhysicalFamilyWitnessV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T12:54:08.075899+00:00
-- url     : https://prove2.me/theorems/b3a07937-2245-4ba4-b7a2-c29c15fab36e
-- title:
--   exercise45LocalisedPhysicalFamilyWitnessV1
-- statement:
--   Fix the large-jump witness to the explicit physical integral, retaining all original remaining obligations. The independent original large-jump grid theorem supplies the removed grid obligation.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii)-(iv).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45LocalisedPhysicalFamilyWitnessV1 :

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
    (X2 : NNReal -> Omega -> Real)
    (hX2Representation : ∀ t omega,
      X2 t omega =
        triplet.drift * (t : Real) +
        ∫ z in Set.prod (Set.Icc (0 : Real) (t : Real))
          {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)),
      let x2Integral : NNReal → Omega → Real := fun t omega =>
        triplet.drift * (∫ s in Set.Icc (0 : Real) (t : Real), fSpace s (Xleft s.toNNReal omega)) +
        ∫ z in Set.Icc (0 : Real) (t : Real) ×ˢ {x : Real | 1 ≤ |x|},
          z.2 * fSpace z.1 (Xleft z.1.toNNReal omega) ∂(N.N omega)
      ∃ (Mfamily : ℕ → NNReal → Omega → Real)
          (stops : Nat -> Omega -> NNReal)
          (integral : NNReal -> Omega -> Real),
          let M : NNReal → Omega → Real := fun t w =>
            if h : ∃ k : ℕ, t ≤ stops k w then Mfamily (Nat.find h) t w else 0
          (∀ᵐ w ∂P, ∀ n m : ℕ, n ≤ m → ∀ t,
            Mfamily m (min t (stops n w)) w = Mfamily n (min t (stops n w)) w) ∧
          (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
            integral t omega = x2Integral t omega + M t omega) ∧
          Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X
            (fun s omega => fSpace (s : Real) (Xleft s omega))
            integral ∧
          (∀ (n : Nat) (t : NNReal),
            MeasurableSet[(F t)] {omega : Omega | stops n omega ≤ t}) ∧
          (∀ᵐ omega : Omega ∂P, Monotone (fun n : Nat => stops n omega)) ∧
          (∀ᵐ omega : Omega ∂P,
            Tendsto (fun n : Nat => (stops n omega : WithTop NNReal))
              atTop (nhds ⊤)) ∧
          (∀ n : Nat, MeasureTheory.Martingale
            (fun t omega => Mfamily n (min t (stops n omega)) omega) F P) ∧
          (∀ᵐ omega : Omega ∂P, ∀ t : NNReal,
            f (t : Real) (X t omega) =
              f 0 (X 0 omega) +
              (∫ s in Set.Icc (0 : Real) (t : Real),
                fTime s (X (Real.toNNReal s) omega) ∂volume) +
              (∫ z in Set.prod (Set.Icc (0 : Real) (t : Real)) Set.univ,
                (f z.1 (Xleft (Real.toNNReal z.1) omega + z.2) -
                 f z.1 (Xleft (Real.toNNReal z.1) omega) -
                 z.2 * fSpace z.1 (Xleft (Real.toNNReal z.1) omega))
                ∂(N.N omega)) + integral t omega) := by
  sorry
end Kyprianou.Ch04
