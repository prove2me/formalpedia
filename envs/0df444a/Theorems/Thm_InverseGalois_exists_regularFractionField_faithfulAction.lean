-- Prove2me | Theorems.Thm_InverseGalois_exists_regularFractionField_faithfulAction
-- name    : InverseGalois.exists_regularFractionField_faithfulAction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T01:39:57.80192+00:00
-- url     : https://prove2.me/theorems/6d9fddb4-9d30-47f0-abdf-e5322b9988f3
-- title:
--   A finite group acts faithfully on its regular rational-function field
-- statement:
--   For every finite group $G$, its left regular action on the variables of a rational-function field extends to a faithful action by field automorphisms. For $L=ℚ(X_g : g∈G)$, the result is
--
--   $$
--   ∀g,h∈G, (∀z∈L, g·z=h·z) ⇒ g=h.
--   $$
--
--   This is the standard regular-representation field used to realize arbitrary finite groups as Galois groups.
--
--   **Formalization Note** The variable set is a universe-zero copy of $G$.
-- source:
--   Mathlib, extension and faithfulness of group actions on fraction fields, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Localization/FractionRing.lean#L648-L676; Cayley's theorem, https://en.wikipedia.org/wiki/Cayley%27s_theorem

import Definitions.Def_InverseGalois_regular_action
import Theorems.Thm_InverseGalois_shrink_faithfulSMul
import Theorems.Thm_InverseGalois_mvPolynomial_faithfulSMul

namespace InverseGalois

universe u

theorem exists_regularFractionField_faithfulAction
    (G : Type u) [Fintype G] [Group G] :
    ∃ action : MulSemiringAction G (RegularFractionField G),
      @FaithfulSMul G (RegularFractionField G) action.toSMul := by sorry
