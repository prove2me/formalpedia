-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_unipotentCompact
-- name    : GroundTheory.Automorphic.Parabolic.isOpen_unipotentCompact
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:16.317828+00:00
-- url     : https://prove2.me/theorems/a5b67b87-f73b-587c-9b95-2e0a6e52f4de
-- title:
--   Parabolic: is Open unipotent Compact
-- statement:
--   The Parabolic construction uses the is Open unipotent Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L129-L133

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

theorem GroundTheory.Automorphic.Parabolic.isOpen_unipotentCompact (e : ℕ) :
    IsOpen (unipotentCompact F n β e : Set (unipotentRadical F n β)) := by sorry
