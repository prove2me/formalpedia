-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompact
-- name    : GroundTheory.Automorphic.Parabolic.isCompact_unipotentCompact
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:11.050901+00:00
-- url     : https://prove2.me/theorems/b28662cc-c06b-4f51-83aa-ad1da12cf9c7
-- title:
--   Parabolic: is Compact unipotent Compact
-- statement:
--   The Parabolic construction uses the is Compact unipotent Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L135-L139

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable (F) (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.isCompact_unipotentCompact (e : ℕ) :
    IsCompact (unipotentCompact F n β e : Set (unipotentRadical F n β)) := by sorry
