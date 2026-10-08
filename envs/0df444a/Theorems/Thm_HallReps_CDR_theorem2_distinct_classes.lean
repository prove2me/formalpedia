-- Prove2me | Theorems.Thm_HallReps_CDR_theorem2_distinct_classes
-- name    : HallReps.CDR.theorem2_distinct_classes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:49:45.76205+00:00
-- url     : https://prove2.me/theorems/dcf6bf78-bda0-42ce-92b9-d4a1b6852ba0
-- title:
--   Theorem 2, p. 29 — representatives from distinct classes exist if any k of the sets meet at least k classes
-- statement:
--   Let $S$ be divided into any number of pairwise disjoint classes (finitely or infinitely many),
--   $$S = S_1 \cup S_2 \cup S_3 \cup \cdots, \qquad S_i \cap S_j = \varnothing \ (i \ne j),$$
--   for instance the classes of an equivalence relation, and let $T_1, \dots, T_m$ be a finite system of subsets of $S$. Suppose that, for each $k = 1, \dots, m$, any $k$ of the sets $T_i$ contain between them elements from at least $k$ classes. Then there exist elements
--   $$a_1, a_2, \dots, a_m, \qquad a_i \in T_i \ (i = 1, \dots, m),$$
--   no two of which belong to the same class.
--
--   Theorem 2 is the "elementary transformation" of Theorem 1 that passes from representatives which are distinct to representatives which lie in distinct classes; Theorem 3 is its special case in which the $T_i$ are themselves the classes of a second partition.
--
--   **Formalization Note.** The partition is given by a class map `cls : α → κ` (the classes are its fibres; `κ` is an arbitrary type, empty classes allowed), which makes the classes cover $S$ and be pairwise disjoint automatically. The system is `T : ι → Set α` with `[Finite ι]`. "The sets $T_i$, $i \in J$, contain elements from at least $|J|$ classes" is `(J.card : ℕ∞) ≤ (cls '' ⋃ i ∈ J, T i).encard`, and "no two in the same class" is injectivity of `cls ∘ a`.
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), p. 29, Theorem 2

import Mathlib

namespace HallReps.CDR

theorem theorem2_distinct_classes {ι α κ : Type*} [Finite ι] (T : ι → Set α)
    (cls : α → κ)
    (h : ∀ s : Finset ι, (s.card : ℕ∞) ≤ (cls '' ⋃ i ∈ s, T i).encard) :
    ∃ a : ι → α, Function.Injective (cls ∘ a) ∧ ∀ i, a i ∈ T i := by sorry

end HallReps.CDR
