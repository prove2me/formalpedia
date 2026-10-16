-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_denominator_bound_aux
-- name    : OAI.ShortEgyptian.denominator_bound_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:16:25.536981+00:00
-- url     : https://prove2.me/theorems/6993711b-c704-447a-8a25-ad36ae0da362
-- title:
--   Doubly exponential bound $(sP)^{2^{k-1}}$ on the denominators of a sorted unit-fraction sum
-- statement:
--   Let $n_1\le n_2\le\dots\le n_k$ be a nondecreasing finite list of positive integers, and let $A,P,s$ be natural numbers with $A>0$, $P>0$ and $k\le s$. If the sum of the reciprocals satisfies
--
--   $$\sum_{i=1}^{k}\frac{1}{n_i}=\frac{A}{P}\quad\text{in }\mathbb{Q},$$
--
--   then every entry satisfies
--
--   $$n_i\le (sP)^{2^{\,k-1}}\qquad(1\le i\le k).$$
--
--   In words: if a sum of $k\le s$ unit fractions equals a positive fraction with denominator $P$, then no denominator exceeds $(sP)^{2^{k-1}}$. Consequently a given positive fraction has only finitely many representations as a sum of a bounded number of unit fractions. This finiteness is what allows extremal arguments over all such representations, for instance to remove repeated denominators, and it also underlies lower bounds for the length of Egyptian fraction expansions.
--
--   **Formalization Note** The sum is `unitSum ns` and sortedness is expressed with `List.Pairwise`. The exponent uses truncated natural subtraction `ns.length - 1`; for the empty list the claim is vacuous.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/LowerBound.lean#L18-L78

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

open OAI OAI.ShortEgyptian

theorem OAI.ShortEgyptian.denominator_bound_aux (ns : List ℕ) (hsort : ns.Pairwise (· ≤ ·))
    (hpos : ∀ n ∈ ns, 0 < n) (A P s : ℕ) (hA : 0 < A) (hP : 0 < P)
    (hlen : ns.length ≤ s) (heq : unitSum ns = (A : ℚ) / P) :
    ∀ n ∈ ns, n ≤ (s * P) ^ (2 ^ (ns.length - 1)) := by sorry
