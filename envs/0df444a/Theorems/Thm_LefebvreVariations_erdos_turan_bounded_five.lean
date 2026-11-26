-- Prove2me | Theorems.Thm_LefebvreVariations_erdos_turan_bounded_five
-- name    : LefebvreVariations.erdos_turan_bounded_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:47:19.066126+00:00
-- url     : https://prove2.me/theorems/386795c0-b43a-40d9-a153-72120b399a18
-- title:
--   Lefebvre's variations, No. 66 — on a theme by Erdős and Turán: no additive basis of order 2 has at most five ordered representations of every integer
-- statement:
--   Let $A\subseteq\mathbb{N}$ be a set such that, for every $n\in\mathbb{N}$, there are at most $5$ ordered pairs $(a,b)\in A\times A$ with $a+b=n$. Then $A$ is not an additive basis of order $2$: there is some $n\in\mathbb{N}$ that is not a sum $a+b$ of two elements of $A$.
--   $$
--   \Bigl(\forall n,\ \#\{(a,b)\in A^2: a+b=n\}\le 5\Bigr)\;\Longrightarrow\;\neg\Bigl(\forall n\in\mathbb{N}\ \exists a,b\in A,\ a+b=n\Bigr).
--   $$
--
--   This is the bound $C=5$ of the Erdős–Turán conjecture on additive bases, which asserts that no additive basis of order $2$ has a bounded representation function. Here the bound is small enough for a finite search.
--
--   **Formalization Note** The count is `{(a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ a + b = n}.ncard`, the number of ordered pairs, so $a+b=n$ and $b+a=n$ with $a\ne b$ count as two representations and $n=2a$ counts once. The set is a subset of a finite set, so `ncard` is the true cardinality. The natural numbers include $0$, so $n=0$ must be represented as $0+0$ for $A$ to be a basis. The conclusion is the negation of: every `n : ℕ` is a sum of two elements of `A`.
--
--   **Why this is a variation.** Variation on the open erdos_turan_additive_bases (the Erdos-Turan conjecture: no additive basis of order 2 has bounded representation function). It is a bounded instance, with the representation function at most 5, small enough for a finite search; it is a partial result and a model for larger bounds.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The Erdős–Turán conjecture on additive bases: P. Erdős and P. Turán, On a problem of Sidon in additive number theory, and on some related problems, J. London Math. Soc. 16 (1941), 212-215 (cited from memory; page numbers not re-checked). Known partial results (that the representation function of any additive basis of order 2 is at least 6 infinitely often, due to Grekos, Haddad, Helou and Pihko, 2003) are recalled from memory and are not verified here; the statement is not claimed to be new. The platform parent is erdos_turan_additive_bases (Open). Truth check performed independently: an exhaustive depth-first search over the membership of 0, 1, 2, ... in A, requiring every n to have between 1 and 5 ordered representations, dies at depth 60.

import Mathlib

namespace LefebvreVariations

/-- The Erdős–Turán conjecture on additive bases (no additive basis of order `2` has a bounded
representation function) at the first bounds that fall to a finite search: if every `n` has at most
`5` ordered representations `n = a + b` with `a, b ∈ A`, then `A` is not an additive basis of order `2`.
(The same search shows the bound `4`, and the parent's statement for every bound `C` is the conjecture itself.)
The set `A` is built one integer at a time: the requirement `1 ≤ r(n) ≤ 5` for each `n` fixes whether
`n ∈ A` up to a few choices, and the tree of admissible choices dies after at most `70` integers.
Source: the conjecture is Erdős and Turán, "On a problem of Sidon in additive number theory, and on
some related problems", J. London Math. Soc. 16 (1941), 212-215; that `r(n) ≥ 6` for infinitely many `n`
for every basis is due to Grekos, Haddad, Helou and Pihko, "On the Erdős-Turán conjecture",
J. Number Theory 102 (2003), 339-352 (both cited from memory); the finite search is ours. -/
theorem erdos_turan_bounded_five (A : Set ℕ)
    (hA : ∀ n : ℕ, {(a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ a + b = n}.ncard ≤ 5) :
    ¬ (∀ n : ℕ, ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ a + b = n) := by
  sorry

end LefebvreVariations
