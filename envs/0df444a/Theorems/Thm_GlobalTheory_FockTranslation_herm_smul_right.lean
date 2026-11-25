-- Prove2me | Theorems.Thm_GlobalTheory_FockTranslation_herm_smul_right
-- name    : GlobalTheory.FockTranslation.herm_smul_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:58.192922+00:00
-- url     : https://prove2.me/theorems/164dcc54-31fe-4810-a530-c5783c953729
-- title:
--   Fock Translation: herm smul right
-- statement:
--   The Fock Translation construction uses the herm smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/FockTranslationLaws.lean#L33-L36

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

theorem GlobalTheory.FockTranslation.herm_smul_right (c : ℂ) (u w : EuclideanSpace ℂ ι) :
    Hf u (c • w) = (starRingEnd ℂ) c * Hf u w := by sorry
