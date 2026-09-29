-- Prove2me | Theorems.Thm_Garrido_exists_fixedPoints_eq_pair_of_ne_one
-- name    : Garrido.exists_fixedPoints_eq_pair_of_ne_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:00:37.81471+00:00
-- url     : https://prove2.me/theorems/fdddb46b-abe7-4226-85f9-e72be4eeb17c
-- title:
--   Theorem 1.7, step — a nontrivial rotation fixes exactly two antipodal points of S²
-- statement:
--   Every rotation $A \in SO(3,\mathbb{R})$ other than the identity fixes exactly two
--   points of the $2$-sphere, and they are antipodal: there is $x \in S^2$ with
--
--   $$\{\, y \in S^2 : Ay = y \,\} = \{x, -x\}.$$
--
--   These are the points where the axis of rotation meets the sphere. Removing all of them, for all
--   rotations in a countable group, is what makes the action of that group on the rest of the
--   sphere free.
--
--   **Formalization Note.** The action is matrix-vector multiplication on `Sphere 2`, and $-x$ is
--   the antipodal point.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, proof of Theorem 1.7; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski

namespace Garrido

theorem exists_fixedPoints_eq_pair_of_ne_one (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hA : A ≠ 1) : ∃ x : Sphere 2, {y : Sphere 2 | A • y = y} = {x, -x} := by
  sorry

end Garrido
