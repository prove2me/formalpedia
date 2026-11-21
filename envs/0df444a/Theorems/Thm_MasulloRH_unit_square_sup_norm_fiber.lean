-- Prove2me | Theorems.Thm_MasulloRH_unit_square_sup_norm_fiber
-- name    : MasulloRH.unit_square_sup_norm_fiber
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:15:17.543887+00:00
-- url     : https://prove2.me/theorems/cc25cde3-3cf6-439f-a356-651d630d627c
-- title:
--   An infinite fiber of the sup norm on an affine line in the plane
-- statement:
--   On the affine line $t\mapsto(1,t)$ in $\mathbb R^2$, equipped with the sup norm, the set of parameters for which the norm equals one is exactly $[-1,1]$ and is infinite. This gives a counterexample to the finite-fiber assertion used in the proof of Lemma 2.2.1.1.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, November 20 draft, proof of Lemma 2.2.1.1, p. 75, immediately after equation (2.2.1.2). The counterexample tests the assertion about fibers of the line parametrization. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=75

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum

open Set

theorem MasulloRH.unit_square_sup_norm_fiber :
    let S := {t : ℝ | ‖fun i : Fin 2 => if i = 0 then (1 : ℝ) else t‖ = 1}
    S = Icc (-1) 1 ∧ S.Infinite := by sorry
