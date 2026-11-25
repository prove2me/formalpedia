-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residue_eq_residue_iff
-- name    : GroundTheory.LocalField.residue_eq_residue_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:27:45.959666+00:00
-- url     : https://prove2.me/theorems/4eab4f0b-54c4-44f9-93f5-03b186338a28
-- title:
--   Local Field: residue eq residue iff
-- statement:
--   The Local Field construction uses the residue eq residue iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L54-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierHaar.lean#L54-L58

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.residue_eq_residue_iff {a b : 𝒪[K]} :
    IsLocalRing.residue 𝒪[K] a = IsLocalRing.residue 𝒪[K] b ↔ (a : K) - b ∈ valBall K 1 := by sorry
