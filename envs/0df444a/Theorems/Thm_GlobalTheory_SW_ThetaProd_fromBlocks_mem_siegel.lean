-- Prove2me | Theorems.Thm_GlobalTheory_SW_ThetaProd_fromBlocks_mem_siegel
-- name    : GlobalTheory.SW.ThetaProd.fromBlocks_mem_siegel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:44:05.310478+00:00
-- url     : https://prove2.me/theorems/9f571dd7-c4da-4d2f-9c19-4167db051603
-- title:
--   Theta Prod: from Blocks mem siegel
-- statement:
--   The Theta Prod construction uses the from Blocks mem siegel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean#L42-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean#L42-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaMulConjEqBlockTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ThetaProd

theorem GlobalTheory.SW.ThetaProd.fromBlocks_mem_siegel {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {τ₁ : Matrix ι₁ ι₁ ℂ} {τ₂ : Matrix ι₂ ι₂ ℂ} (h₁ : τ₁ ∈ Siegel ι₁) (h₂ : τ₂ ∈ Siegel ι₂) :
    Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) := by sorry
