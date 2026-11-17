-- Prove2me | Theorems.Thm_Kyprianou_Ch07_portStoneFourierTransienceCriterion
-- name    : Kyprianou.Ch07.portStoneFourierTransienceCriterion
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T14:45:58.848211+00:00
-- url     : https://prove2.me/theorems/53e61673-107b-42c6-8dd7-a00c7a509d60
-- title:
--   Theorem 7.4: Port–Stone Fourier criterion for transience
-- statement:
--   For a Lévy process X with characteristic exponent Ψ, transience is equivalent to finiteness of the integral of the real part of 1/Ψ(θ) over some sufficiently small symmetric interval around zero. Otherwise the process is recurrent. Finiteness is represented by Lebesgue integrability on the interval, with the exponent tied to the complete time-indexed characteristic function E exp(iθX_t)=exp(-tΨ(θ)). The integral is evaluated only on a sufficiently small punctured neighbourhood where the characteristic exponent is nonzero. This explicit domain condition excludes the identically-zero exponent; the book (p.184) leaves the singularity convention implicit.
-- source:
--   Kyprianou (2006), first edition, Theorem 7.4, printed p.184; Windows Ky.pdf landscape sheet 97 (original single-page p.193).

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_TransienceAndRecurrence
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Theorem 7.4: Port–Stone Fourier criterion for transience
and the complementary recurrence class. The Fourier reciprocal
is required to be defined on a punctured neighbourhood of zero;
Lean's totalised inverse otherwise misclassifies the zero process. -/
theorem portStoneFourierTransienceCriterion
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (Psi : Real → Complex)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hExponent : ∀ (t : NNReal) (theta : Real),
      (∫ omega, Complex.exp
        (Complex.I * (theta : Complex) * (X t omega : Complex)) ∂P) =
      Complex.exp (-((t : Real) : Complex) * Psi theta)) :
    let finiteFourierOccupation : Prop :=
      ∃ epsilon : Real, 0 < epsilon ∧
        (∀ theta : Real, theta ∈ Set.Ioo (-epsilon) epsilon →
          theta ≠ 0 → Psi theta ≠ 0) ∧
        IntegrableOn (fun theta : Real => (1 / Psi theta).re)
          (Set.Ioo (-epsilon) epsilon) volume
    (IsTransientLevyProcess P X ↔ finiteFourierOccupation) ∧
    (IsRecurrentLevyProcess P X ↔ ¬ finiteFourierOccupation) := by
  sorry

end Kyprianou.Ch07
