-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_comp_glueP_one
-- name    : GlobalTheory.Phase.Doubling.comp_glueP_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:44:31.970985+00:00
-- url     : https://prove2.me/theorems/4860c9fd-c3ad-4408-8587-3d9be7cbc9ba
-- title:
--   Doubling: comp glue P one
-- statement:
--   The Doubling construction uses the comp glue P one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L72-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}

theorem GlobalTheory.Phase.Doubling.comp_glueP_one (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 1 (glueP (a, b)) = b := by sorry
