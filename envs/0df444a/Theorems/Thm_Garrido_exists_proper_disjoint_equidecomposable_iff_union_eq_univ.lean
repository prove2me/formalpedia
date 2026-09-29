-- Prove2me | Theorems.Thm_Garrido_exists_proper_disjoint_equidecomposable_iff_union_eq_univ
-- name    : Garrido.exists_proper_disjoint_equidecomposable_iff_union_eq_univ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:08:24.535438+00:00
-- url     : https://prove2.me/theorems/f04e1db5-5b9c-49d2-874b-6136dab01fcb
-- title:
--   Corollary 1.3 — the two forms of a paradoxical decomposition agree
-- statement:
--   For a group $G$ acting on a set $X$, the following are equivalent:
--
--   1. there are proper disjoint $A, B \subseteq X$ with $A \sim X$ and $B \sim X$;
--   2. there are proper disjoint $A, B \subseteq X$ with $A \cup B = X$, $A \sim X$ and
--      $B \sim X$;
--
--   where $\sim$ is $G$-equidecomposability and "proper" is written as $\neq X$. Direction
--   (2) $\Rightarrow$ (1) is immediate; the content is (1) $\Rightarrow$ (2), that the two pieces
--   can be taken to cover $X$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 2, Corollary 1.3; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Equidecomposability

namespace Garrido

theorem exists_proper_disjoint_equidecomposable_iff_union_eq_univ
    {G X : Type*} [Group G] [MulAction G X] :
    (∃ A B : Set X, A ≠ Set.univ ∧ B ≠ Set.univ ∧ Disjoint A B ∧
        Equidecomposable G A Set.univ ∧ Equidecomposable G B Set.univ) ↔
      (∃ A B : Set X, A ≠ Set.univ ∧ B ≠ Set.univ ∧ Disjoint A B ∧ A ∪ B = Set.univ ∧
        Equidecomposable G A Set.univ ∧ Equidecomposable G B Set.univ) := by
  sorry

end Garrido
