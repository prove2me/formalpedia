-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_dup_apply
-- name    : GlobalTheory.Phase.Doubling.dup_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:46.011345+00:00
-- url     : https://prove2.me/theorems/1dbc5a0a-526b-4d32-ac87-e916d035fe32
-- title:
--   Doubling: dup apply
-- statement:
--   The Doubling construction uses the dup apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L29-L30

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

theorem GlobalTheory.Phase.Doubling.dup_apply (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    dup φ x = φ (rowM 0 x) * φ (rowM 1 x) := by sorry
