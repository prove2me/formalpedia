-- Prove2me | Theorems.Thm_HurwitzQ_normSq_omega
-- name    : HurwitzQ.normSq_omega
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:09:06.630133+00:00
-- url     : https://prove2.me/theorems/cfd56f51-fecf-46c9-ad4e-b6b78a5ac75d
-- title:
--   Squared norm of the Hurwitz generator
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Put $\omega=(1+i+j+k)/2$, where $i,j,k$ are the standard quaternion units. Write $N(a+bi+cj+dk)=a^2+b^2+c^2+d^2$ for the squared norm.
--
--   $$
--   N(\omega)=1.
--   $$
--
--   The half-integral generator has squared norm one.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_omega
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.NormNum

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.normSq_omega : normSq omega = 1 := by sorry
