-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_compactOpen_unipotentRadical
-- name    : GroundTheory.Automorphic.Parabolic.exists_compactOpen_unipotentRadical
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:52.174835+00:00
-- url     : https://prove2.me/theorems/d3a88f56-7c83-5886-a404-33f6fbed6566
-- title:
--   Parabolic: exists compact Open unipotent Radical
-- statement:
--   The Parabolic construction uses the exists compact Open unipotent Radical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L152-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L152-L165

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

theorem GroundTheory.Automorphic.Parabolic.exists_compactOpen_unipotentRadical (s : Finset (unipotentRadical F n β)) :
    ∃ K : Subgroup (unipotentRadical F n β), IsCompact (K : Set (unipotentRadical F n β)) ∧
      IsOpen (K : Set (unipotentRadical F n β)) ∧ ∀ x ∈ s, x ∈ K := by sorry
