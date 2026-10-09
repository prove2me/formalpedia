-- Prove2me | Theorems.Thm_HurwitzQ_not_allIntCoordsQ_and_allHalfIntCoordsQ
-- name    : HurwitzQ.not_allIntCoordsQ_and_allHalfIntCoordsQ
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:09:20.433742+00:00
-- url     : https://prove2.me/theorems/d34a10cd-d2ae-47ac-ae85-6af59d3ba115
-- title:
--   Disjoint coordinate branches of the Hurwitz integers
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Let $q$ be a rational quaternion.
--
--   $$
--   \neg\bigl((a,b,c,d\in\mathbb{Z})\land(a,b,c,d\in\mathbb{Z}+\tfrac12)\bigr),\qquad q=a+bi+cj+dk.
--   $$
--
--   The two alternatives in the Hurwitz coordinate criterion cannot hold simultaneously.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.not_allIntCoordsQ_and_allHalfIntCoordsQ (q : ℍ[ℚ]) :
    ¬ (allIntCoordsQ q ∧ allHalfIntCoordsQ q) := by sorry
