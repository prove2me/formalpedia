-- Prove2me | Theorems.Thm_HurwitzQ_normSq_nat
-- name    : HurwitzQ.normSq_nat
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:08:38.514289+00:00
-- url     : https://prove2.me/theorems/39bbbe89-2392-4257-b100-a479ee08b9fa
-- title:
--   The squared norm of a Hurwitz integer is a natural number
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Write $N(a+bi+cj+dk)=a^2+b^2+c^2+d^2$ for the squared norm. Let $q$ be a rational quaternion.
--
--   $$
--   q\in\mathcal{H}\implies\exists n\in\mathbb{N},\quad N(q)=n.
--   $$
--
--   This supplies the natural-valued size function for arithmetic in the Hurwitz ring.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.normSq_nat (q : ℍ[ℚ]) (hq : q ∈ hurwitzIntegersQ) : ∃ n : ℕ, normSq q = n := by sorry
