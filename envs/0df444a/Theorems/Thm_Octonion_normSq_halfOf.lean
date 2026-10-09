-- Prove2me | Theorems.Thm_Octonion_normSq_halfOf
-- name    : Octonion.normSq_halfOf
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:44.457908+00:00
-- url     : https://prove2.me/theorems/ff06f84a-f009-4163-9914-d9369cc9e65a
-- title:
--   Squared norm in doubled integer coordinates
-- statement:
--   Write $N(x)=\sum_{i=0}^7 x_i^2$ for the squared norm in the coordinate order $(a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3)$. For $a\in\mathbb Z^8$, let $a/2$ denote the rational octonion with coordinates $a_i/2$.
--
--   $$
--   N(a/2)=\frac14\sum_{i=0}^7 a_i^2.
--   $$
--
--   This translates norm equations into integer sums of squares.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_normSq_halfOf.lean, line 9; SHA-256 97b710aab29a998f06fc0efc789c9acb32a63e970cd0eb982ede09ac8b363bb9. No public source repository is claimed.

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators

theorem Octonion.normSq_halfOf (a : Fin 8 → ℤ) :
    normSq (halfOf a) = (∑ i : Fin 8, ((a i : ℚ))^2) / 4 := by sorry
