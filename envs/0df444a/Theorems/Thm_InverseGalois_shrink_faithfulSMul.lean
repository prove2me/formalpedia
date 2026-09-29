-- Prove2me | Theorems.Thm_InverseGalois_shrink_faithfulSMul
-- name    : InverseGalois.shrink_faithfulSMul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T01:34:54.666661+00:00
-- url     : https://prove2.me/theorems/98a37c19-32c2-4c7d-ae4e-b0582d5851bf
-- title:
--   Faithfulness of the regular action on a universe shrink
-- statement:
--   Let $G$ be a finite group. Transport the left regular action of $G$ to a universe-zero copy of its underlying type. This action is faithful:
--
--   $$
--   [∀x, g · x = h · x] ⇒ g=h.
--   $$
--
--   This universe-polymorphic form of the regular action is useful when a construction must remain in the lowest universe.
--
--   **Formalization Note** `Shrink G` is equivalent to $G$ but lives in universe zero.
-- source:
--   Cayley's theorem, regular action formulation, https://en.wikipedia.org/wiki/Cayley%27s_theorem

import Mathlib

namespace InverseGalois

universe u

theorem shrink_faithfulSMul {G : Type u} [Fintype G] [Group G] :
    FaithfulSMul G (Shrink.{0} G) := by sorry
