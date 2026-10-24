-- Prove2me | Theorems.Thm_OAI_CommonBasesFPRAS_positive_count_iff_common_independent
-- name    : OAI.CommonBasesFPRAS.positive_count_iff_common_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-23T21:31:43.525436+00:00
-- url     : https://prove2.me/theorems/c0badf74-9e52-4817-bfb7-cc9ff092f3d1
-- title:
--   Positive common-base count and full-rank common independence
-- statement:
--   Let $M_1$ and $M_2$ be matroids with elements in a common finite ambient set of size $n$, both of rank $r$. Write $Z$ for their number of common bases. Then
--
--   $$Z>0\quad\Longleftrightarrow\quad\exists I,\ |I|=r\ \text{and }I\text{ is independent in both }M_1\text{ and }M_2.$$
--
--   This is the feasibility characterization used before approximate counting. It identifies the positive-count case without asserting a running-time bound.
--
--   **Formalization Note.** The count is the existing mission's CommonBasesFPRAS common-base count.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FeasibilitySolver.lean#L24-L49 — commonBaseCount_pos_iff_common_independent; adapted from the source finite-set cardinality to the existing mission’s equivalent Nat.card definition.

import Definitions.Def_CommonBasesFPRAS

open OAI.CommonBasesFPRAS

theorem OAI.CommonBasesFPRAS.positive_count_iff_common_independent (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (hr₁ : M₁.eRank = (r : ℕ∞)) (hr₂ : M₂.eRank = (r : ℕ∞)) :
    0 < commonBaseCount M₁ M₂ ↔
      ∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by sorry
