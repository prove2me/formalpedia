-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_apply_le_one_of_mem_archCompact
-- name    : GroundTheory.Automorphic.Reduction.norm_apply_le_one_of_mem_archCompact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:11.012197+00:00
-- url     : https://prove2.me/theorems/39a8a4af-8f52-5517-acf3-e1a7941b3a0c
-- title:
--   Reduction: norm apply le one of mem arch Compact
-- statement:
--   The Reduction construction uses the norm apply le one of mem arch Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L118-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L118-L129

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.norm_apply_le_one_of_mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) (i j : Fin n) : ‖k i j‖ ≤ 1 := by sorry
