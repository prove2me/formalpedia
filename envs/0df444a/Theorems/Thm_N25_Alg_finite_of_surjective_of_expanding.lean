-- Prove2me | Theorems.Thm_N25_Alg_finite_of_surjective_of_expanding
-- name    : N25.Alg.finite_of_surjective_of_expanding
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T01:21:32.33447+00:00
-- url     : https://prove2.me/theorems/b5471f48-3756-4117-bef1-5346abbdc65d
-- title:
--   Surjective expanding maps on Northcott sets have finite domain
-- statement:
--   If f : X -> X is surjective and q has finite sublevel sets with q(f x) >= c q(x) - C for some c > 1, then X is finite.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib

namespace N25.Alg
theorem finite_of_surjective_of_expanding {X : Type*} (f : X → X) (hf : Function.Surjective f)
    (q : X → ℝ) (hq : ∀ B : ℝ, {x | q x ≤ B}.Finite) (c C : ℝ) (hc : 1 < c)
    (h : ∀ x, c * q x - C ≤ q (f x)) : Finite X := by sorry
end N25.Alg
