-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45ActualPureJumpReconstructionV1
-- name    : Kyprianou.Ch04.exercise45ActualPureJumpReconstructionV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-27T00:20:07.931632+00:00
-- url     : https://prove2.me/theorems/f9a882b1-7631-5a8a-ad8c-2b4ccae979e4
-- title:
--   Original-space pure-jump Lévy cutoff reconstruction
-- statement:
--   For a pure-jump Levy process with the given characteristic triplet and actual Poisson jump measure, the compensated finite-cutoff states converge as the positive cutoff goes to zero, almost surely simultaneously at every time.
-- source:
--   Kyprianou (2006), Exercise 4.5 and Levy-Ito decomposition, Chapter 2.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45ActualPureJumpReconstructionV1 :
∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    [SigmaFinite triplet.levyMeasure]
    (hNoGaussian : triplet.gaussianVariance = 0)
    (hTriplet : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (N : PoissonRandomMeasure.{0,0,0}
      P triplet.levyMeasure)
    (Xleft : NNReal -> Omega -> Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, ∀ t : NNReal, 0 < t ->
      Tendsto (fun s : NNReal => X s omega)
        (nhdsWithin t (Set.Iio t)) (nhds (Xleft t omega)))
    (hLeftZero : ∀ᵐ w ∂P, Xleft 0 w = X 0 w)
    (hNLaw : ∀ᵐ omega : Omega ∂P,
      N.N omega = Kyprianou.Ch04.pathJumpMeasure X Xleft omega),
    let X2 : NNReal → Omega → ℝ := fun t w =>
      triplet.drift * (t : ℝ) +
        ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂(N.N w)
    let Y : ℝ → NNReal → Omega → ℝ := fun e t w =>
      X2 t w + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 ∂(N.N w)) -
        (t : ℝ) * ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂triplet.levyMeasure
    ∀ᵐ w ∂P, ∀ t : NNReal,
      Tendsto (fun e : ℝ => Y e t w) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X t w)) := by
  sorry
end Kyprianou.Ch04
