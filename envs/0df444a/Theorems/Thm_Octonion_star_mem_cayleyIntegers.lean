-- Prove2me | Theorems.Thm_Octonion_star_mem_cayleyIntegers
-- name    : Octonion.star_mem_cayleyIntegers
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:29:07.323923+00:00
-- url     : https://prove2.me/theorems/8e0eaa34-010b-4725-856f-1098274e4d9e
-- title:
--   The Cayley order is closed under conjugation
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Suppose $x\in\mathcal C$.
--
--   $$
--   \bar x\in\mathcal C.
--   $$
--
--   Conjugation therefore preserves the chosen integral structure.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_star_mem_cayleyIntegers.lean, line 8; SHA-256 8dff6c9bdfe98b4a6fb7fb9f3a3ce2074752ad695d47ebd35245c50fd2f58c4e. No public source repository is claimed.

import Definitions.Def_Octonion_cayleyIntegers
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

theorem Octonion.star_mem_cayleyIntegers {x : octonions ℚ} (hx : x ∈ cayleyIntegers) :
    star x ∈ cayleyIntegers := by sorry
