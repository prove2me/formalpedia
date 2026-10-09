-- Prove2me | Theorems.Thm_Octonion_mem_cayleyUnits_iff
-- name    : Octonion.mem_cayleyUnits_iff
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:42.02997+00:00
-- url     : https://prove2.me/theorems/e6af7d41-612b-4a04-8985-7bf91eb92dc5
-- title:
--   Complete classification of the units of the Cayley order
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Let $U$ consist of the sixteen signed coordinate vectors $\pm e_i$ and all vectors supported on a weight-four mask in $M$, with each supported coordinate independently equal to $\pm\tfrac12$. Call $x$ a unit of $\mathcal C$ when $x\in\mathcal C$ and there is $y\in\mathcal C$ with $xy=yx=1$. Let $x\in\mathbb O_{\mathbb Q}$.
--
--   $$
--   x\in U\iff x\text{ is a unit of }\mathcal C.
--   $$
--
--   Together with the cardinality theorem, this gives an exhaustive finite classification of the 240 units.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_mem_cayleyUnits_iff.lean, line 9; SHA-256 b8e6d9560ab82bc742e5bd30d465ebec9106828724611918fc3c949d5f083a78. No public source repository is claimed.

import Definitions.Def_Octonion_IsCayleyUnit
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators

theorem Octonion.mem_cayleyUnits_iff {x : octonions ℚ} : x ∈ cayleyUnits ↔ IsCayleyUnit x := by sorry
