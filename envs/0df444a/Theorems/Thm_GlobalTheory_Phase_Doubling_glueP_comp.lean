-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_glueP_comp
-- name    : GlobalTheory.Phase.Doubling.glueP_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:44:37.719872+00:00
-- url     : https://prove2.me/theorems/9c3694a8-2bb0-40a9-afcb-73159c2fcf6d
-- title:
--   Doubling: glue P comp
-- statement:
--   The Doubling construction uses the glue P comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L77-L80

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

theorem GlobalTheory.Phase.Doubling.glueP_comp (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    glueP (comp 0 y, comp 1 y) = y := by sorry
