-- Prove2me | Theorems.Thm_MatSemiBurnside_diameter_le_card
-- name    : MatSemiBurnside.diameter_le_card
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:26.325198+00:00
-- url     : https://prove2.me/theorems/ae252997-e6cd-488f-8942-c95c669b7cb9
-- title:
--   Diameter at most cardinality
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite and nonempty and $\sim$ a congruence on $\langle X\rangle$ with finite quotient. Then every class of $\langle X\rangle/\sim$ has length at most $|\langle X\rangle/\sim|$: every $a\in\langle X\rangle$ is congruent to a product $a_1\cdots a_k$ of elements of $X$ with
--   $$1\le k\le|\langle X\rangle/\sim|.$$
--
--   So the diameter of a finite quotient is at most its cardinality; this gives the diameter half of Theorem 1 from the cardinality half.
--
--   Differences from the source:
--   - encoding: "its length is at most the cardinality of the quotient" for a product of minimum length in its class → `DiameterLE X c (Nat.card c.Quotient)` under `Finite c.Quotient`; reason: every class has a minimum-length representative, so both say every class has length at most |⟨X⟩/∼|
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, p.31

import Mathlib
import Definitions.Def_MatSemiBurnside_IsProdRepr
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Diameter at most cardinality.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, p.31: "Finally, a product
of minimum length in its class has pairwise incongruent nonempty prefix products. Otherwise, the
factor between two congruent prefixes could be omitted to obtain a shorter representative. Its
length is therefore at most the cardinality of the quotient."

**Formalization Note.** For a finite quotient ⟨X⟩/∼, every class has length at most |⟨X⟩/∼|
(`Nat.card`, which is the true cardinality since the quotient is finite). -/
theorem diameter_le_card {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (hX : X.Nonempty)
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (hfin : Finite c.Quotient) :
    DiameterLE X c (Nat.card c.Quotient) := by sorry

end MatSemiBurnside
