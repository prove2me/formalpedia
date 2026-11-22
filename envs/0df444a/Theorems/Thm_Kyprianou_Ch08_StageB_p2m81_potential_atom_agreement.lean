-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m81_potential_atom_agreement
-- name    : Kyprianou.Ch08.StageB.p2m81_potential_atom_agreement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T00:38:58.846121+00:00
-- url     : https://prove2.me/theorems/3b26378e-7ffb-42c3-b0b5-654ad00a8b82
-- title:
--   Potentials with the same Laplace agree on positive singletons
-- statement:
--   Two half-line measures with the same Laplace transform s/f(s) assign the same mass to every positive singleton. Proved by exponential tilting to finite measures and the Proved complex-MGF uniqueness theorem with Mathlib analyticity. Identifies atoms across scales in the parent bridge.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m81_potential_atom_agreement
    (f : ℝ → ℝ) (hpos : ∀ s : ℝ, 0 < s → 0 < f s)
    (ν1 ν2 : Measure ℝ)
    (h1supp : ν1 (Iio (0 : ℝ)) = 0)
    (h2supp : ν2 (Iio (0 : ℝ)) = 0)
    (h1lap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν1) = ENNReal.ofReal (s / f s))
    (h2lap : ∀ s : ℝ, 0 < s →
      (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-s * y)) ∂ν2) = ENNReal.ofReal (s / f s))
    (x : ℝ) (hx : 0 < x) : ν1 {x} = ν2 {x} := by
  sorry
