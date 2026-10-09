-- Prove2me | Theorems.Thm_Octonion_isCayleyUnit_iff_normSq
-- name    : Octonion.isCayleyUnit_iff_normSq
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:41.56818+00:00
-- url     : https://prove2.me/theorems/dddb79f1-5050-4615-b3e1-89fb48f96bc0
-- title:
--   Cayley units are exactly the elements of squared norm one
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Write $N(x)=\sum_{i=0}^7 x_i^2$ for the squared norm in the coordinate order $(a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3)$. Call $x$ a unit of $\mathcal C$ when $x\in\mathcal C$ and there is $y\in\mathcal C$ with $xy=yx=1$. Suppose $x\in\mathcal C$.
--
--   $$
--   x\text{ is a unit of }\mathcal C\iff N(x)=1.
--   $$
--
--   This reduces the arithmetic unit condition to a quadratic equation.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_isCayleyUnit_iff_normSq.lean, line 21; SHA-256 042e5a0a7a6a263e93284a72270dfe3f32fa010c3c8f38882953aaf5984f8365. No public source repository is claimed.

import Definitions.Def_Octonion_IsCayleyUnit
import Definitions.Def_Octonion_cayleyIntegers
import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators

theorem Octonion.isCayleyUnit_iff_normSq {x : octonions ℚ} (hx : isCayley x) :
    IsCayleyUnit x ↔ normSq x = 1 := by sorry
