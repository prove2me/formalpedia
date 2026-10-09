-- Prove2me | Theorems.Thm_Octonion_cayleyUnits_isCayley_normSq_one
-- name    : Octonion.cayleyUnits_isCayley_normSq_one
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:33.090371+00:00
-- url     : https://prove2.me/theorems/e3d2016e-bc45-44b7-bd83-ba4bf313de87
-- title:
--   Every listed Cayley unit belongs to the order and has squared norm one
-- statement:
--   Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Write $N(x)=\sum_{i=0}^7 x_i^2$ for the squared norm in the coordinate order $(a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3)$. Let $U$ consist of the sixteen signed coordinate vectors $\pm e_i$ and all vectors supported on a weight-four mask in $M$, with each supported coordinate independently equal to $\pm\tfrac12$.
--
--   $$
--   u\in U\implies u\in\mathcal C\ \land\ N(u)=1.
--   $$
--
--   This establishes the validity of the finite list.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_cayleyUnits_isCayley_normSq_one.lean, line 27; SHA-256 79dc0a0658a8b3c36abc7acbd8338be855dca04a5ecbcf0180a10c9e2e79d2c8. No public source repository is claimed.

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_cayleyUnits
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators

theorem Octonion.cayleyUnits_isCayley_normSq_one : ∀ u ∈ cayleyUnits, isCayley u ∧ normSq u = 1 := by sorry
