-- Prove2me | Theorems.Thm_Kyprianou_Ch06_exponentialSampledVectorLevyIsInfinitelyDivisible
-- name    : Kyprianou.Ch06.exponentialSampledVectorLevyIsInfinitelyDivisible
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:10:33.187703+00:00
-- url     : https://prove2.me/theorems/44f8507c-20e1-4adf-b9af-4c3f54bb5a01
-- title:
--   Lemma 6.17: exponential sampling is bivariate infinitely divisible
-- statement:
--   For any d-dimensional Lévy process and independent Exp(p) observation time, the joint time-position vector is infinitely divisible, expressed by an nth convolution-root characteristic function for every positive integer n. Its joint characteristic function also equals the full Lévy–Khintchine/Frullani integral ∫₀∞∫_{R^d}(1−exp(iϑt+iθ·x))e^(−pt)P(X_t∈dx)dt/t and the rational factor p/(p−iϑ+Ψ(θ)). Both formulas and all spatial dimensions are retained.
-- source:
--   Kyprianou (2006), Lemma 6.17, printed p. 160; two-up PDF p. 85.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_VectorLevyProcess
import Definitions.Def_Kyprianou_Ch06_TimePositionCharFun
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Lemma 6.17: an independent exponential observation time makes
the joint time-position vector infinitely divisible; its characteristic
function has both the Frullani-Levy integral representation and the
rational characteristic-exponent representation. -/
theorem exponentialSampledVectorLevyIsInfinitelyDivisible
    {Omega : Type} [MeasurableSpace Omega]
    (d : Nat) (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → (Fin d → Real))
    (e : Omega → NNReal) (p : Real)
    (psi : (Fin d → Real) → Complex)
    (hp : 0 < p)
    (hX : IsVectorLevyProcess d P X)
    (hExp : ∀ t : NNReal,
      P {omega | t < e omega} =
        ENNReal.ofReal (Real.exp (-p * (t : Real))))
    (hExpIndependent :
      ∀ (k : Nat) (times : Fin k → NNReal)
        (A : Fin k → Set (Fin d → Real)) (B : Set NNReal),
        (∀ i, MeasurableSet (A i)) → MeasurableSet B →
        P {omega | e omega ∈ B ∧
          (∀ i : Fin k, X (times i) omega ∈ A i)} =
          P {omega | e omega ∈ B} *
          P {omega | ∀ i : Fin k, X (times i) omega ∈ A i})
    (hPsi : ∀ (t : NNReal) (theta : Fin d → Real),
      (∫ omega,
        Complex.exp (Complex.I *
          (↑(∑ i : Fin d, theta i * X t omega i) : Complex)) ∂P) =
      Complex.exp (-(↑(t : Real) : Complex) * psi theta))
    (hJointMeas : Measurable
      (fun omega => (e omega, X (e omega) omega))) :
    let mu : Measure (NNReal × (Fin d → Real)) :=
      Measure.map (fun omega => (e omega, X (e omega) omega)) P
    (∀ n : Nat, 0 < n →
      ∃ nu : Measure (NNReal × (Fin d → Real)),
        IsProbabilityMeasure nu ∧
        ∀ (vartheta : Real) (theta : Fin d → Real),
          TimePositionCharFun d mu vartheta theta =
            (TimePositionCharFun d nu vartheta theta) ^ n) ∧
    (∀ (vartheta : Real) (theta : Fin d → Real),
      TimePositionCharFun d mu vartheta theta =
        Complex.exp (-
          (∫ t in Set.Ioi (0 : Real),
            (Complex.exp (-(↑(p * t) : Complex)) /
               (↑t : Complex)) *
            (1 - ∫ omega,
              Complex.exp (Complex.I *
                (↑(vartheta * t +
                  ∑ i : Fin d, theta i *
                    X t.toNNReal omega i) : Complex)) ∂P) ∂volume)) ∧
      TimePositionCharFun d mu vartheta theta =
        (↑p : Complex) /
          ((↑p : Complex) -
            Complex.I * (↑vartheta : Complex) + psi theta)) := by
  sorry

end Kyprianou.Ch06
