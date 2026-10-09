-- Prove2me | Theorems.Thm_HurwitzQ_normSq_nat_pos
-- name    : HurwitzQ.normSq_nat_pos
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:08:52.326498+00:00
-- url     : https://prove2.me/theorems/76feda83-2eef-4728-ae73-6c6599d28509
-- title:
--   A nonzero Hurwitz integer has positive squared norm
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Write $N(a+bi+cj+dk)=a^2+b^2+c^2+d^2$ for the squared norm. Let $q$ be a rational quaternion.
--
--   $$
--   q\in\mathcal{H},\ q\ne0\implies\exists n\in\mathbb{N},\quad n\ne0\ \land\ N(q)=n.
--   $$
--
--   In particular, the squared norm of a nonzero Hurwitz integer is at least one.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.normSq_nat_pos (q : ℍ[ℚ]) (hq : q ∈ hurwitzIntegersQ) (h0 : q ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ normSq q = n := by sorry
