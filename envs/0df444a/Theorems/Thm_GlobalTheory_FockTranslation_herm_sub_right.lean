-- Prove2me | Theorems.Thm_GlobalTheory_FockTranslation_herm_sub_right
-- name    : GlobalTheory.FockTranslation.herm_sub_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:06.663309+00:00
-- url     : https://prove2.me/theorems/7e95292b-8d81-43b9-aa8e-39b3011b0ad8
-- title:
--   Fock Translation: herm sub right
-- statement:
--   The Fock Translation construction uses the herm sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L21-L22

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

theorem GlobalTheory.FockTranslation.herm_sub_right (u v w : EuclideanSpace ℂ ι) : Hf u (v - w) = Hf u v - Hf u w := by sorry
