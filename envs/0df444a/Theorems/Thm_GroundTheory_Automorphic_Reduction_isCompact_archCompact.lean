-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_isCompact_archCompact
-- name    : GroundTheory.Automorphic.Reduction.isCompact_archCompact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:57:57.486831+00:00
-- url     : https://prove2.me/theorems/91a356e2-15c5-508c-ace5-4301997b9257
-- title:
--   Reduction: is Compact arch Compact
-- statement:
--   The Reduction construction uses the is Compact arch Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L131-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L131-L154

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

theorem GroundTheory.Automorphic.Reduction.isCompact_archCompact (w : InfinitePlace K) :
    IsCompact (archCompact (n := n) w : Set (GL (Fin n) w.Completion)) := by sorry
