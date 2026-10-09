-- Prove2me | Theorems.Thm_HurwitzQ_omega_sq
-- name    : HurwitzQ.omega_sq
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:09:44.377034+00:00
-- url     : https://prove2.me/theorems/76cf8775-38f8-40b7-ac4f-d1fef18af6b4
-- title:
--   Quadratic relation for the Hurwitz generator
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Put $\omega=(1+i+j+k)/2$, where $i,j,k$ are the standard quaternion units.
--
--   $$
--   \omega^2=\omega-1.
--   $$
--
--   This gives a polynomial relation for the half-integral generator.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_omega
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NormNum

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.omega_sq : omega ^ 2 = omega - 1 := by sorry
