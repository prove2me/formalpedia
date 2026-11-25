-- Prove2me | Theorems.Thm_GlobalTheory_FockTranslation_herm_sub_swap
-- name    : GlobalTheory.FockTranslation.herm_sub_swap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:03:04.258855+00:00
-- url     : https://prove2.me/theorems/38e25d53-b2ab-4ffa-a2ab-b7b20d22ad63
-- title:
--   Fock Translation: herm sub swap
-- statement:
--   The Fock Translation construction uses the herm sub swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L42-L47

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

theorem GlobalTheory.FockTranslation.herm_sub_swap (u w : EuclideanSpace ℂ ι) :
    Hf w u = Hf u w - 2 * I * ((Hf u w).im : ℂ) := by sorry
