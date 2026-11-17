-- Prove2me | Theorems.Thm_Kyprianou_Ch07_exercise7_6CreepingHittingAllParts
-- name    : Kyprianou.Ch07.exercise7_6CreepingHittingAllParts
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:54:35.145444+00:00
-- url     : https://prove2.me/theorems/dce92d6f-c48f-4d45-b69f-5454cf4804ad
-- title:
--   Exercise 7.6: all five creeping, variation and point-hitting claims
-- statement:
--   Exercise 7.6, preserving all five subparts: (i) the high-frequency Lévy characteristic exponent satisfies Ψ(θ)/θ²→σ²/2 as |θ|→∞, and creeping both upwards and downwards is equivalent to a nonzero Gaussian component; (ii) for bounded variation, upward creeping is equivalent to strictly positive canonical drift d; (iii) irregularity of 0 for the positive half-line precludes upward creeping; (iv) a spectrally negative Lévy process without Gaussian component and excluding the negative of a subordinator cannot creep downwards; (v) a symmetric α-stable process with α∈(1,2) does not creep in either direction yet hits every point with positive probability.
-- source:
--   Kyprianou (2006), Exercise 7.6(i)–(v), printed pp.208–209; original PDF physical pp.217–218; Windows Ky.pdf sheets 109–110.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.6(i)–(v), with distinct hypotheses for each case. -/
theorem exercise7_6CreepingHittingAllParts
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (↑(theta * X t omega) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * Psi theta)) :
    let upCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1
    let downCreeps : Prop :=
      0 < Kyprianou.Ch05.creepingProbability
        P (fun t omega => -X t omega)
          (fun _ => (⊤ : WithTop NNReal)) 1
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    ((Tendsto (fun theta : Real =>
         Psi theta / ((theta ^ 2 : Real) : Complex))
         (Filter.comap (fun theta : Real => |theta|) atTop)
         (nhds (((sigma2 : Real) / 2 : Real) : Complex)) ∧
       ((upCreeps ∧ downCreeps) ↔ 0 < sigma2)) ∧
     ((sigma2 = 0 ∧ finiteVariationJumpMass) →
       (upCreeps ↔ 0 < canonicalDrift)) ∧
     (Kyprianou.Ch06.IsIrregularFor P X 0 (Set.Ioi 0) →
       ¬ upCreeps) ∧
     (sigma2 = 0 → Pi (Set.Ioi 0) = 0 →
       (¬ ∀ᵐ omega ∂P,
         Monotone (fun t : NNReal => -X t omega)) →
       ¬ downCreeps) ∧
     (∀ alpha : Real, 1 < alpha → alpha < 2 →
       (∃ c : Real, 0 < c ∧ ∀ theta : Real,
         Psi theta = ((c * |theta| ^ alpha : Real) : Complex)) →
       (¬ upCreeps ∧ ¬ downCreeps ∧
         ∀ x : Real, 0 < P {omega : Omega |
           ∃ t : NNReal, 0 < t ∧ X t omega = x}))) := by
  sorry

end Kyprianou.Ch07
