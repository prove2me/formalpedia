-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedPhysicalDataV1
-- name    : Kyprianou.Ch04.exercise45LocalisedPhysicalDataV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T23:35:52.743615+00:00
-- url     : https://prove2.me/theorems/23af5af8-7f80-4bc7-9a34-f6dfa571963a
-- title:
--   Physical bounded cutoff data on cofinal finite exits
-- statement:
--   Prepare bounded physical integral and residual witnesses on cofinal finite exit clocks, with the original derivative and finite variation terms on closed prefixes and the residual on strict prefixes, and stopped martingales.
-- source:
--   Kyprianou Exercise 4.5

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open Kyprianou.Ch04 MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45LocalisedPhysicalDataV1 :
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
          {x : Real | 1 ≤ |x|}, z.2 ∂(N.N omega)),
    let H (a : ℝ → ℝ → ℝ) : NNReal → Omega → ℝ := fun t w => a (t : ℝ) (Xleft t w)
    let D (a : ℝ → ℝ → ℝ) : NNReal → Omega → ℝ := fun t w =>
      triplet.drift * (∫ s in Icc (0 : ℝ) (t : ℝ), a s (Xleft s.toNNReal w)) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
          z.2 * a z.1 (Xleft z.1.toNNReal w) ∂(N.N w)
    let R (a atime ax : ℝ → ℝ → ℝ) : NNReal → Omega → ℝ := fun t w =>
      a (t : ℝ) (X t w) - (a 0 (X 0 w) +
        (∫ s in Icc (0 : ℝ) (t : ℝ), atime s (X s.toNNReal w) ∂volume) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
          (a z.1 (Xleft z.1.toNNReal w + z.2) - a z.1 (Xleft z.1.toNNReal w) -
            z.2 * ax z.1 (Xleft z.1.toNNReal w)) ∂(N.N w)))
    ∃ (Hn Dn Rn Mn : ℕ → NNReal → Omega → ℝ) (τ : ℕ → Omega → NNReal),
      (∀ n t, MeasurableSet[F t] {w | τ n w ≤ t}) ∧
      (∀ w, Monotone (fun n => τ n w)) ∧
      (∀ᵐ w ∂P, Tendsto (fun n => (τ n w : WithTop NNReal)) atTop (nhds ⊤)) ∧
      (∀ᵐ w ∂P, ∀ n t, t ≤ τ n w → Hn n t w = H fSpace t w ∧ Dn n t w = D fSpace t w) ∧
      (∀ᵐ w ∂P, ∀ n t, t < τ n w → Rn n t w = R f fTime fSpace t w) ∧
      (∀ n, IsStochasticIntegralInProbabilityV2 P X (Hn n) (fun t w => Dn n t w + Mn n t w)) ∧
      (∀ n, ∀ᵐ w ∂P, ∀ t, Rn n t w = Dn n t w + Mn n t w) ∧
      (∀ n, Martingale (fun t w => Mn n (min t (τ n w)) w) F P) := by
  sorry
end Kyprianou.Ch04
