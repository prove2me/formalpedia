-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_house_star
-- name    : GlobalTheory.SmoothForms.house_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:49.174936+00:00
-- url     : https://prove2.me/theorems/7bd5b613-9e7e-485a-b8ef-84e9c670fb5c
-- title:
--   Smooth Forms: house star
-- statement:
--   The Smooth Forms construction uses the house star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsLieDataCircle.lean#L128-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsLieDataCircle.lean#L128-L137

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open scoped ContDiff Topology
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SmoothForms.house_star (a : E) : house (star a) = house a := by sorry
