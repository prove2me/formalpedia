-- Prove2me | Theorems.Thm_GlobalTheory_FockTranslation_herm_add_left
-- name    : GlobalTheory.FockTranslation.herm_add_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:03:03.634915+00:00
-- url     : https://prove2.me/theorems/db280fe9-ab89-40db-897d-eb0795a3905c
-- title:
--   Fock Translation: herm add left
-- statement:
--   The Fock Translation construction uses the herm add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L12-L13

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

theorem GlobalTheory.FockTranslation.herm_add_left (u v w : EuclideanSpace ℂ ι) : Hf (u + v) w = Hf u w + Hf v w := by sorry
