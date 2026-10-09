-- Prove2me | Theorems.Thm_Octonion_omega1_mem
-- name    : Octonion.omega1_mem
-- status  : Proved
-- author  : @jawneeboy
-- created : 2026-09-23T13:28:57.285253+00:00
-- url     : https://prove2.me/theorems/66fddc96-709b-436d-acee-55dcb997b01e
-- title:
--   The first Hurwitz half-vector belongs to the Cayley order
-- statement:
--   Let $\mathcal C\subset\mathbb O_{\mathbb Q}$ be the chosen Cayley order: $x=a/2$ for $a\in\mathbb Z^8$, with the mask $\sum_{a_i\text{ odd}}2^i$ in $M=\{0,15,51,60,86,89,101,106,149,154,166,169,195,204,240,255\}$. Put $\omega_1=((1+i+j+k)/2,0)$ in quaternion-pair coordinates.
--
--   $$
--   \omega_1\in\mathcal C.
--   $$
--
--   This records a useful half-integral element in the first quaternion slot.
-- source:
--   Standard reference: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345. Relevant topics appear in Chapter 6 (composition algebras), Chapter 9 (octavian integers), and Section 10.1 (the 240 octavian units), as confirmed by the publisher's table of contents. Supporting exposition: John Baez, Integral Octonions (Part 6), September 17, 2013, https://math.ucr.edu/home/baez/octonions/integers/integers_6.html. These references concern the classical mathematics. This contribution supplies Lean definitions and machine-checked proofs in the stated coordinate convention; it does not claim new mathematical results or reproduce a particular proof from the book. The topic references do not assert that the exact Lean statement occurs there. Verification of the book references is limited to its table of contents, not a statement-by-statement comparison with the book; no page-specific or numbered theorem attribution is claimed. Local formalization: Basic/Thm_Octonion_generators_mem_cayleyIntegers.lean, line 18; SHA-256 f26591b55a62c81b458a7b4ebb8cdfe1e58c532d543c4e4cd1dbe711d378c4bc. No public source repository is claimed.

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

theorem Octonion.omega1_mem :
    (⟨⟨(1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ), (1 / 2 : ℚ)⟩, 0⟩ : octonions ℚ) ∈
      cayleyIntegers := by sorry
