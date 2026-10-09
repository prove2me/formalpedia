-- Prove2me | Theorems.Thm_Octonion_conj_mul
-- name    : Octonion.conj_mul
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:36.540055+00:00
-- url     : https://prove2.me/theorems/448727fb-00c6-4443-965e-8826ee906ea2
-- title:
--   Conjugate times an octonion equals its squared norm
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Write $N(x)=\sum_{i=0}^7 x_i^2$ for the squared norm in the coordinate order $(a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3)$. Let $x\in\mathbb O_{\mathbb Q}$.
--
--   $$
--   \bar x x=N(x)\,1.
--   $$
--
--   This supplies the conjugate on the left, independently of the product with the conjugate on the right.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_conj_mul.lean, line 9; SHA-256 5f0d095157d9b1141a0cb4cf23f9aa0ddfb78b995c7392a6ffe5c1dca80db404. No public source repository is claimed.

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

theorem Octonion.conj_mul (x : octonions ℚ) : conj x * x = ⟨⟨normSq x, 0, 0, 0⟩, 0⟩ := by sorry
