-- Prove2me | Theorems.Thm_GlobalTheory_FockTranslation_herm_zero_right
-- name    : GlobalTheory.FockTranslation.herm_zero_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:59.777147+00:00
-- url     : https://prove2.me/theorems/5c18ca0b-41c3-418d-a5c8-a5e6124dbede
-- title:
--   Fock Translation: herm zero right
-- statement:
--   The Fock Translation construction uses the herm zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L30-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory.FockTranslation
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.FockTranslation.herm_zero_right (u : EuclideanSpace ℂ ι) : Hf u 0 = 0 := by sorry
