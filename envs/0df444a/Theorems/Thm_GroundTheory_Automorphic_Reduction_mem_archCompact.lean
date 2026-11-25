-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_mem_archCompact
-- name    : GroundTheory.Automorphic.Reduction.mem_archCompact
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:15.67889+00:00
-- url     : https://prove2.me/theorems/bf68d412-e867-4fcb-a160-7e2b1dd49179
-- title:
--   Reduction: mem arch Compact
-- statement:
--   The Reduction construction uses the mem arch Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L113-L116

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

theorem GroundTheory.Automorphic.Reduction.mem_archCompact {w : InfinitePlace K} {k : GL (Fin n) w.Completion} :
    k ∈ archCompact w ↔ ∀ y : Fin n → w.Completion,
      euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y := by sorry
