-- Prove2me | Theorems.Thm_Octonion_normSq_one
-- name    : Octonion.normSq_one
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:56.12977+00:00
-- url     : https://prove2.me/theorems/dbb40ae3-9cf8-4ed3-92d8-32fa33700f0c
-- title:
--   The rational octonion identity has squared norm one
-- statement:
--   Use the Cayley–Dickson model $\mathbb O_R=\mathbb H_R\times\mathbb H_R$, with $(a,b)(c,d)=(ac-\bar d b,da+b\bar c)$ and $\overline{(a,b)}=(\bar a,-b)$. Write $N(x)=\sum_{i=0}^7 x_i^2$ for the squared norm in the coordinate order $(a_0,a_1,a_2,a_3,b_0,b_1,b_2,b_3)$. Work over $R=\mathbb Q$.
--
--   $$
--   N(1)=1.
--   $$
--
--   This gives the normalization of the squared norm at the multiplicative identity.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_normSq_one.lean, line 6; SHA-256 6c4741e0e18d0012fbf0bf2f912d772081a04b8036ee806c87c12d5d14ce837f. No public source repository is claimed.

import Definitions.Def_Octonion_normSq
import Definitions.Def_Octonion_octonions
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

open Quaternion Octonion BigOperators

theorem Octonion.normSq_one : normSq (1 : octonions ℚ) = 1 := by sorry
