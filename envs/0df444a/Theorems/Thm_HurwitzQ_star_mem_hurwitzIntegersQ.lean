-- Prove2me | Theorems.Thm_HurwitzQ_star_mem_hurwitzIntegersQ
-- name    : HurwitzQ.star_mem_hurwitzIntegersQ
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-18T18:09:55.001582+00:00
-- url     : https://prove2.me/theorems/84bbc968-1399-4365-a3cf-9cc888c79c45
-- title:
--   Hurwitz integers are closed under conjugation
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. Let $q$ be a rational quaternion.
--
--   $$
--   q\in\mathcal{H}\implies\overline q\in\mathcal{H}.
--   $$
--
--   Here $\overline{a+bi+cj+dk}=a-bi-cj-dk$. Conjugation therefore restricts to the Hurwitz ring.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345 The displayed assertion is an elementary consequence of this definition; no numbered theorem attribution is claimed.

import Definitions.Def_HurwitzQ_hurwitzIntegersQ
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

open Quaternion QuaternionAlgebra HurwitzQ

theorem HurwitzQ.star_mem_hurwitzIntegersQ {q : ℍ[ℚ]} (hq : q ∈ hurwitzIntegersQ) :
    star q ∈ hurwitzIntegersQ := by sorry
