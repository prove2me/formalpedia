-- Prove2me | Theorems.Thm_Kyprianou_Ch04_expProductClockWienerHopfChar
-- name    : Kyprianou.Ch04.expProductClockWienerHopfChar
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T07:56:45.773069+00:00
-- url     : https://prove2.me/theorems/9280a461-efc0-4d67-b6f5-99405e1c98a8
-- title:
--   Joint characteristic transform on the exponential product clock
-- statement:
--   Use Avram's proved product-clock independence and exponential supremum law. Factor the joint characteristic function, recover the signed drawdown characteristic function from the terminal characteristic function by dividing by the nonzero supremum factor, then evaluate the requested product.
-- source:
--   Kyprianou (2006), Exercise 4.8(ii), Wiener–Hopf transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.expProductClockWienerHopfChar
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (Psi : ℝ → ℂ)
    (hPsi : ∀ (t : NNReal) (theta : ℝ),
      (∫ ω, Complex.exp (Complex.I * (theta : ℂ) * (L.X t ω : ℂ)) ∂P) =
        Complex.exp (-((t : ℝ) : ℂ) * Psi theta))
    (q : ℝ) (hq : 0 < q)
    (phi : ℝ) (hphi : 0 < phi) (hroot : L.ψ phi = q)
    (a b : ℝ) :
    let S : Ω × ℝ → ℝ := fun z => runningSup L z.2.toNNReal z.1
    let D : Ω × ℝ → ℝ := fun z => L.X z.2.toNNReal z.1 - S z
    (∫ z, Complex.exp (Complex.I * (a : ℂ) * (D z : ℂ) +
      Complex.I * (b : ℂ) * (S z : ℂ)) ∂(P.prod (expMeasure q))) =
      ((q : ℂ) * ((phi : ℂ) - Complex.I * (a : ℂ))) /
        ((Psi a + (q : ℂ)) * ((phi : ℂ) - Complex.I * (b : ℂ))) := by
  sorry
