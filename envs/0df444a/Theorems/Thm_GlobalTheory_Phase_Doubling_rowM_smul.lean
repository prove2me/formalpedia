-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_rowM_smul
-- name    : GlobalTheory.Phase.Doubling.rowM_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:43:33.929992+00:00
-- url     : https://prove2.me/theorems/1879f820-8397-4c4e-94fa-51654198f074
-- title:
--   Doubling: row M smul
-- statement:
--   The Doubling construction uses the row M smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L38-L39

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

theorem GlobalTheory.Phase.Doubling.rowM_smul (j : Fin 2) (c : ℚ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (c • x) = c • rowM j x := by sorry
