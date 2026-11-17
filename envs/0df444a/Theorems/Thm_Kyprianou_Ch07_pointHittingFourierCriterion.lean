-- Prove2me | Theorems.Thm_Kyprianou_Ch07_pointHittingFourierCriterion
-- name    : Kyprianou.Ch07.pointHittingFourierCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:53:03.162091+00:00
-- url     : https://prove2.me/theorems/24086ebb-7a98-47b5-bc44-94ce392b3c51
-- title:
--   Theorem 7.12: point-hitting Fourier integral and all three Lévy triplet cases
-- statement:
--   For a non-compound-Poisson real Lévy process with characteristic exponent Ψ and actual Lévy–Khintchine triplet, the set C of real points x hit at a strictly positive time with positive probability is nonempty if and only if ∫_ℝ Re[(1+Ψ(u))⁻¹]du is finite. The Gaussian case gives C=ℝ. With zero Gaussian component and unbounded variation, finiteness again gives C=ℝ. With bounded variation, the Fourier condition holds exactly when the canonical finite-variation drift d is nonzero, and C=ℝ unless X or −X is a subordinator, giving C=(0,∞) or (−∞,0), respectively.
-- source:
--   Kyprianou (2006), Theorem 7.12, printed p.199, source single-page PDF p.208, Windows Ky.pdf sheet 105.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.12: the Kesten–Bretagnolle point-hitting criterion,
including the Gaussian, infinite-variation and bounded-variation cases. -/
theorem pointHittingFourierCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta)) :
    let C : Set Real := {x | 0 < P
       {omega : Omega | ∃ t : NNReal, 0 < t ∧ X t omega = x}}
    let hitsCriterion : Prop :=
      Integrable (fun theta : Real =>
        ((1 : Complex) / (1 + Psi theta)).re) volume
    let jumpFiniteVariation : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let finiteVariation : Prop := sigma2 = 0 ∧ jumpFiniteVariation
    let effectiveDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    let upwardsSubordinator : Prop :=
      ∀ᵐ omega ∂P, Monotone (fun t : NNReal => X t omega)
    let downwardsSubordinator : Prop :=
      ∀ᵐ omega ∂P, Monotone (fun t : NNReal => -X t omega)
    ((C.Nonempty ↔ hitsCriterion) ∧
     (0 < sigma2 → hitsCriterion ∧ C = Set.univ) ∧
     (sigma2 = 0 → ¬ jumpFiniteVariation →
       hitsCriterion → C = Set.univ) ∧
     (finiteVariation →
       ((hitsCriterion ↔ effectiveDrift ≠ 0) ∧
        (effectiveDrift ≠ 0 →
          ((upwardsSubordinator → C = Set.Ioi 0) ∧
           (downwardsSubordinator → C = Set.Iio 0) ∧
           (¬ upwardsSubordinator → ¬ downwardsSubordinator →
             C = Set.univ)))))) := by
  sorry

end Kyprianou.Ch07
