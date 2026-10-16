-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_remove_repetitions
-- name    : OAI.ShortEgyptian.remove_repetitions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:18:09.108744+00:00
-- url     : https://prove2.me/theorems/54496ad7-03b6-4126-8fb1-6684fc9bf120
-- title:
--   Repeated denominators can be removed without changing the number of unit fractions
-- statement:
--   For natural numbers $a,b$, an *expansion* of $a/b$ is a strictly increasing finite sequence $n_1<\dots<n_k$ of natural numbers, all at least $2$, with $\sum_i 1/n_i=a/b$ in $\mathbb{Q}$.
--
--   Let $a,b$ be natural numbers with $0<a<b$, and let $m_1,\dots,m_k$ be a finite list of positive integers, in any order and possibly with repetitions, such that
--
--   $$\sum_{i=1}^{k}\frac{1}{m_i}=\frac ab .$$
--
--   Then there is an expansion $n_1<\dots<n_k$ of $a/b$ with exactly the same number $k$ of terms.
--
--   Thus, to bound the length of the shortest Egyptian fraction expansion of a proper fraction, it suffices to write it as a sum of unit fractions in which denominators may repeat. In the proof of the $O(\log\log b)$ upper bound, the representation of $a/b$ is assembled from several pieces whose denominators need not be distinct, and this result converts it into a genuine expansion of the same length.
--
--   **Formalization Note** The hypothesis is stated with `unitSum ns`, the rational sum of the reciprocals of the list `ns`, and the conclusion is `IsExpansion a b xs` together with equality of the list lengths.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/Distinctness.lean#L63-L129

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

open OAI OAI.ShortEgyptian

theorem OAI.ShortEgyptian.remove_repetitions {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (ns : List ℕ) (hpos : ∀ n ∈ ns, 0 < n) (heq : unitSum ns = (a : ℚ) / b) :
    ∃ xs : List ℕ, IsExpansion a b xs ∧ xs.length = ns.length := by sorry
