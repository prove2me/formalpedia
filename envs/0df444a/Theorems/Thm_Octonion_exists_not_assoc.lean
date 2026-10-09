-- Prove2me | Theorems.Thm_Octonion_exists_not_assoc
-- name    : Octonion.exists_not_assoc
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:35.40238+00:00
-- url     : https://prove2.me/theorems/fa9b11a3-3420-4d68-9996-06eeff687f57
-- title:
--   Rational octonion multiplication is not associative
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Work over $R=\mathbb Q$.
--
--   $$
--   \exists x,y,z\in\mathbb O_{\mathbb Q},\quad (xy)z\ne x(yz).
--   $$
--
--   This shows why an associative ring interface does not describe rational octonions.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_exists_not_assoc.lean, line 6; SHA-256 1ba7e67bec466f3a200da032337ed7e6db34bd8e96e43ed9e8aaad9bab13d810. No public source repository is claimed.

import Definitions.Def_Octonion_octonions
import Definitions.Def_Octonion_toRat8
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators

theorem Octonion.exists_not_assoc : ∃ x y z : octonions ℚ, (x * y) * z ≠ x * (y * z) := by sorry
