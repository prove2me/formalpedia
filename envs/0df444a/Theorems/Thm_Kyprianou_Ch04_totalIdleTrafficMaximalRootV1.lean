-- Prove2me | Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
-- name    : Kyprianou.Ch04.totalIdleTrafficMaximalRootV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:56:26.160563+00:00
-- url     : https://prove2.me/theorems/d3060c86-b471-4ab8-822c-83abfe8c8ea3
-- title:
--   Positive bounded-variation drift gives nonmonotone-downward input and classifies the maximal zero root by traffic
-- statement:
--   For the same spectrally negative bounded-variation model, positive uncompensated drift excludes a.s. antitone paths, and the maximal nonnegative zero of psi is positive exactly in the overloaded regime. Use the finite-variation Lévy exponent d*theta minus the integral of 1-exp(theta*y); the right derivative at zero is d minus the extended jump first moment, and strict positivity in the light/critical case follows from strict exponential inequality, including the zero jump measure case. The extended moment argument covers infinite mean.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, p. 89 and Chapter 3 upward first-passage classification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.totalIdleTrafficMaximalRootV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    : let rho : ENNReal :=
      (∫⁻ y : Real, ENNReal.ofReal (-y) ∂L.ν) /
        ENNReal.ofReal L.drift
    (¬ (∀ᵐ omega : Omega ∂P,
      Antitone (fun t : NNReal => L.X t omega))) ∧
    (∀ phi : Real, 0 ≤ phi → L.ψ phi = 0 →
      (∀ theta : Real, 0 ≤ theta → L.ψ theta = 0 → theta ≤ phi) →
      (rho > 1 → 0 < phi) ∧ (rho ≤ 1 → phi = 0)) := by
  sorry
