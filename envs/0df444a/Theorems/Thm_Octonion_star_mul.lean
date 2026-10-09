-- Prove2me | Theorems.Thm_Octonion_star_mul
-- name    : Octonion.star_mul
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:29:03.565854+00:00
-- url     : https://prove2.me/theorems/871cc8d8-7812-4dfb-b941-dcdafd2824b3
-- title:
--   Octonion conjugation reverses multiplication
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Let $R$ be any commutative ring and $x,y\in\mathbb O_R$.
--
--   $$
--   \overline{xy}=\bar y\bar x.
--   $$
--
--   This expresses compatibility of conjugation with the noncommutative product.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_star_mul.lean, line 9; SHA-256 95f4e46f2ced01c313aae93eee7a4afd994973243de2f7a32a96a68eb33e1a2f. No public source repository is claimed.

import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators
variable {R : Type*} [CommRing R]

theorem Octonion.star_mul (x y : octonions R) : star (x * y) = star y * star x := by sorry
