-- Prove2me | Theorems.Thm_GlobalTheory_Phase_Doubling_expo_row
-- name    : GlobalTheory.Phase.Doubling.expo_row
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:54.972207+00:00
-- url     : https://prove2.me/theorems/bb360a8d-ffbf-4a83-8ccf-a485d52feed2
-- title:
--   Doubling: expo row
-- statement:
--   The Doubling construction uses the expo row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L201-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DoubledRowTestFunctionProperties.lean#L201-L207

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

theorem GlobalTheory.Phase.Doubling.expo_row (τ : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin 2 → Fin n × Fin g → ℂ) (j : Fin 2)
    (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    qv (x j) ⬝ᵥ blk n τ *ᵥ qv (x j) + 2 * (qv (x j) ⬝ᵥ ζ j) =
      ∑ k, (qv (rowM j x k) ⬝ᵥ τ *ᵥ qv (rowM j x k) +
        2 * (qv (rowM j x k) ⬝ᵥ (fun k i => ζ j (k, i)) k)) := by sorry
