-- Prove2me | Theorems.Thm_GlobalTheory_LevQuot_exists_subgroup_of_finite
-- name    : GlobalTheory.LevQuot.exists_subgroup_of_finite
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:23.971101+00:00
-- url     : https://prove2.me/theorems/5a6da5d0-9f49-409e-a9cc-ae4c58c18379
-- title:
--   Lev Quot: exists subgroup of finite
-- statement:
--   The Lev Quot construction uses the exists subgroup of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L153-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean#L153-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}

theorem GlobalTheory.LevQuot.exists_subgroup_of_finite {G : Type} [Group G] (S : Submonoid G) [Finite S] :
    ∃ T : Subgroup G, ∀ g, g ∈ T ↔ g ∈ S := by sorry
