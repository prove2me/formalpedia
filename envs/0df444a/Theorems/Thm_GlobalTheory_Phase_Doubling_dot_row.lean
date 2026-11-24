-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_dot_row
-- name    : GlobalTheory.Phase.Doubling.dot_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:16:12.927856+00:00
-- url     : https://prove2.me/theorems/fcf03011-eb5c-4377-a02a-b4000f8664aa
-- title:
--   Doubling: dot row
-- statement:
--   The Doubling construction uses the dot row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L48-L50

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

theorem GlobalTheory.Phase.Doubling.dot_row (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    x j ⬝ᵥ y j = ∑ k, rowM j x k ⬝ᵥ rowM j y k := by sorry
