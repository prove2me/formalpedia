-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_upper_mul_archCompact
-- name    : GroundTheory.Automorphic.Reduction.exists_upper_mul_archCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:45.763275+00:00
-- url     : https://prove2.me/theorems/89f18608-754b-5acb-ab7b-fc2d5206bb3b
-- title:
--   Reduction: exists upper mul arch Compact
-- statement:
--   The Reduction construction uses the exists upper mul arch Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L156-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L156-L166

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

theorem GroundTheory.Automorphic.Reduction.exists_upper_mul_archCompact (w : InfinitePlace K) (h : GL (Fin n) w.Completion) :
    ∃ b : GL (Fin n) w.Completion, (b : Matrix (Fin n) (Fin n) w.Completion).IsUpperTriangular ∧
      ∃ k ∈ archCompact w, h = b * k := by sorry
