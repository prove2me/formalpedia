-- Prove2me | Theorems.Thm_GlobalTheory_surjective_of_isOpenMap_of_compact_of_divisible
-- name    : GlobalTheory.surjective_of_isOpenMap_of_compact_of_divisible
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:55.846241+00:00
-- url     : https://prove2.me/theorems/7b15718b-75c3-4e9e-a244-ebd5f9243d96
-- title:
--   Global Theory: surjective of is Open Map of compact of divisible
-- statement:
--   The Global Theory construction uses the surjective of is Open Map of compact of divisible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L40-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V A : Type*} [NormedAddCommGroup V] [AddCommGroup A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] {e : V →+ A}

theorem GlobalTheory.surjective_of_isOpenMap_of_compact_of_divisible [CompactSpace A] (he : IsOpenMap e)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ a : A, ∃ b : A, n • b = a) : Function.Surjective e := by sorry
