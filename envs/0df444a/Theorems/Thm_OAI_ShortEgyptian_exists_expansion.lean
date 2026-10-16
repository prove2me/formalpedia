-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_exists_expansion
-- name    : OAI.ShortEgyptian.exists_expansion
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:15:53.681606+00:00
-- url     : https://prove2.me/theorems/4d968032-d3a6-432e-b93b-07577c2136ab
-- title:
--   Every fraction $a/b$ with $a<b$ has an Egyptian fraction expansion
-- statement:
--   For natural numbers $a$ and $b$, an *expansion* of $a/b$ is a finite strictly increasing sequence $n_1<n_2<\dots<n_k$ of natural numbers, all at least $2$, such that $\frac1{n_1}+\cdots+\frac1{n_k}=\frac ab$ in $\mathbb{Q}$.
--
--   **Theorem.** For all natural numbers $a$ and $b$ with $a<b$, the fraction $a/b$ has an expansion:
--
--   $$
--   a<b\ \Longrightarrow\ \exists\,k\ge0,\ \exists\,2\le n_1<\dots<n_k:\quad \frac ab=\sum_{i=1}^{k}\frac{1}{n_i}.
--   $$
--
--   For $a=0$ the empty sequence is an expansion. This is the existence half of the main theorem on short Egyptian fractions: every proper fraction is a sum of distinct unit fractions, so for $1\le a<b$ the shortest expansion length of $a/b$ is the minimum of a nonempty set of natural numbers.
--
--   **Formalization Note** Expansions are lists `ns` satisfying `IsExpansion a b ns`: the list is pairwise strictly increasing (`List.Pairwise`), every entry is at least $2$, and the sum of the reciprocals, computed in $\mathbb{Q}$, equals $a/b$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/GreedyExistence.lean#L7-L61

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic

open OAI OAI.ShortEgyptian

theorem OAI.ShortEgyptian.exists_expansion (a b : ℕ) (hab : a < b) :
    ∃ ns : List ℕ, IsExpansion a b ns := by sorry
