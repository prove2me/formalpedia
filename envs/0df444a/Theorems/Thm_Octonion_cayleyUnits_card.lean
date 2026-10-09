-- Prove2me | Theorems.Thm_Octonion_cayleyUnits_card
-- name    : Octonion.cayleyUnits_card
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:31.273974+00:00
-- url     : https://prove2.me/theorems/02a0cd3d-4dc2-4d8a-91c0-36a4aa5d122c
-- title:
--   The Cayley unit list contains 240 elements
-- statement:
--   Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Let $U$ consist of the sixteen signed coordinate vectors $\pm e_i$ and all vectors supported on a weight-four mask in $M$, with each supported coordinate independently equal to $\pm\tfrac12$.
--
--   $$
--   |U|=240.
--   $$
--
--   Together with the unit classification, this counts all units of the order.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_cayleyUnits_card.lean, line 42; SHA-256 03e31c378d2f9edb4c3156de59d13dd772aa2e71acd5d08eacf03bb057e769e9. No public source repository is claimed.

import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_cayleyUnits
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

theorem Octonion.cayleyUnits_card : cayleyUnits.card = 240 := by sorry
