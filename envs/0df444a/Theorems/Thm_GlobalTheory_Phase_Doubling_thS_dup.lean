-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_thS_dup
-- name    : GlobalTheory.Phase.Doubling.thS_dup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:44:22.741395+00:00
-- url     : https://prove2.me/theorems/098aba54-4d25-41ca-bd7f-969cb7b81ec4
-- title:
--   Doubling: th S dup
-- statement:
--   The Doubling construction uses the th S dup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L209-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L209-L221

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

theorem GlobalTheory.Phase.Doubling.thS_dup {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ Siegel (Fin g)) (ζ : Fin 2 → Fin n × Fin g → ℂ) :
    thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i)) := by sorry
