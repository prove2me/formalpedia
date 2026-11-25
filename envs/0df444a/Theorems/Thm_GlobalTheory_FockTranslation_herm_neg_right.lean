-- Prove2me | Theorems.Thm_GlobalTheory_FockTranslation_herm_neg_right
-- name    : GlobalTheory.FockTranslation.herm_neg_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:07.765955+00:00
-- url     : https://prove2.me/theorems/0e527c5e-65a6-4428-99d6-a1ed3db4fe74
-- title:
--   Fock Translation: herm neg right
-- statement:
--   The Fock Translation construction uses the herm neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L27-L28

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

theorem GlobalTheory.FockTranslation.herm_neg_right (u w : EuclideanSpace ℂ ι) : Hf u (-w) = -Hf u w := by sorry
