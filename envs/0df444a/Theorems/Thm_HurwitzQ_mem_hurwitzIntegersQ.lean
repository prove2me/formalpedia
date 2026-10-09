-- Prove2me | Theorems.Thm_HurwitzQ_mem_hurwitzIntegersQ
-- name    : HurwitzQ.mem_hurwitzIntegersQ
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:08:18.886502+00:00
-- url     : https://prove2.me/theorems/f5af49a1-6499-4eaf-b86d-ccf199804db3
-- title:
--   Coordinate characterization of Hurwitz integers
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Let $q$ be a rational quaternion.
--
--   $$
--   q\in\mathcal{H}\iff (a,b,c,d\in\mathbb{Z})\ \lor\ (a,b,c,d\in\mathbb{Z}+\tfrac12),\qquad q=a+bi+cj+dk.
--   $$
--
--   This exposes the coordinate criterion for membership in the subring.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.mem_hurwitzIntegersQ (q : ℍ[ℚ]) :
    q ∈ hurwitzIntegersQ ↔ allIntCoordsQ q ∨ allHalfIntCoordsQ q := by sorry
