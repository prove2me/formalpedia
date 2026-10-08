-- Prove2me | Theorems.Thm_HallReps_CDR_theorem3_common_representatives
-- name    : HallReps.CDR.theorem3_common_representatives
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:49:43.885993+00:00
-- url     : https://prove2.me/theorems/e6713bc9-90ba-4fd5-a344-79bf2e99dd51
-- title:
--   Theorem 3, pp. 29–30 — two partitions into m classes have a common system of representatives if any k classes of one meet ≥ k classes of the other
-- statement:
--   Let a set $S$ (finite or infinite) be divided into $m$ classes in two different ways,
--   $$S = S_1 \cup S_2 \cup \cdots \cup S_m, \qquad S = S_1' \cup S_2' \cup \cdots \cup S_m',$$
--   with $S_i \cap S_j = S_i' \cap S_j' = \varnothing$ for $i \ne j$. Suppose that, for each $k = 1, 2, \dots, m$, any $k$ of the classes $S_j'$ contain between them elements from at least $k$ of the classes $S_i$. Then, possibly after permuting the suffixes of the $S_j'$, there are $m$ elements $a_1, \dots, a_m$ of $S$ with
--   $$a_i \in S_i \cap S_i' \qquad (i = 1, 2, \dots, m).$$
--   Equivalently, there is a permutation $\sigma$ of $\{1, \dots, m\}$ and elements $a_i \in S_i \cap S_{\sigma(i)}'$, so that $\{a_1, \dots, a_m\}$ is at the same time a complete system of representatives for both partitions.
--
--   This is the paper's criterion for a common system of representatives of two classifications, without König's assumption that all classes have the same size; König's theorem (equal finite class sizes) is the special case in which the proviso holds automatically.
--
--   **Formalization Note.** The partitions are class maps `p q : α → Fin m`, with $S_i = p^{-1}(i)$ and $S_j' = q^{-1}(j)$; classes are not assumed non-empty (the hypothesis forces it) and `α` is not assumed finite. For a set $J$ of indices, the classes $S_i$ met by $\bigcup_{j \in J} S_j'$ are `p '' (q ⁻¹' J)`, a subset of `Fin m`, so `Set.ncard` is its true size. The permutation `σ` is existential and chosen together with the representatives; $a_i \in S_i \cap S'_{\sigma(i)}$ is `p (a i) = i ∧ q (a i) = σ i`, which makes the $a_i$ automatically distinct.
-- source:
--   P. Hall, On representatives of subsets, J. London Math. Soc. 10 (1935), pp. 29–30, Theorem 3

import Mathlib

namespace HallReps.CDR

theorem theorem3_common_representatives {α : Type*} {m : ℕ} (p q : α → Fin m)
    (h : ∀ s : Finset (Fin m), s.card ≤ (p '' (q ⁻¹' (s : Set (Fin m)))).ncard) :
    ∃ σ : Equiv.Perm (Fin m), ∃ a : Fin m → α, ∀ i, p (a i) = i ∧ q (a i) = σ i := by sorry

end HallReps.CDR
