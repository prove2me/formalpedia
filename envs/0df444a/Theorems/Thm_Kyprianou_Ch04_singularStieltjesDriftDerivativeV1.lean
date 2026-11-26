-- Prove2me | Theorems.Thm_Kyprianou_Ch04_singularStieltjesDriftDerivativeV1
-- name    : Kyprianou.Ch04.singularStieltjesDriftDerivativeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:27:19.491806+00:00
-- url     : https://prove2.me/theorems/fb6038c4-61f8-5147-81fc-b7811fbe5b43
-- title:
--   Almost-everywhere derivative of a linear drift plus singular Stieltjes components
-- statement:
--   The Radon-Nikodym derivatives vanish almost everywhere by singularity; apply the Stieltjes differentiation theorem and derivative arithmetic.
-- source:
--   Supporting proof for Kyprianou (2006), Chapter 4, Exercise 4.9(i).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.singularStieltjesDriftDerivativeV1 (p q : StieltjesFunction ℝ)
    (hp : p.measure.MutuallySingular volume)
    (hq : q.measure.MutuallySingular volume) (d : ℝ) :
    ∀ᵐ x : ℝ ∂volume, HasDerivAt (fun t : ℝ => d * t + p t - q t) d x := by
  sorry
