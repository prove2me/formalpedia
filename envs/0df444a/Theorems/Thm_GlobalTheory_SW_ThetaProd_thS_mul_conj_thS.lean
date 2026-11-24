-- Prove2me | Theorems.Thm_GlobalTheory_SW_ThetaProd_thS_mul_conj_thS
-- name    : GlobalTheory.SW.ThetaProd.thS_mul_conj_thS
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:44:27.286849+00:00
-- url     : https://prove2.me/theorems/dc5937ce-201f-4b05-be5c-e001029e1013
-- title:
--   Theta Prod: th S mul conj th S
-- statement:
--   The Theta Prod construction uses the th S mul conj th S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean#L90-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaMulConjEqBlockTheta.lean#L90-L102

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

theorem GlobalTheory.SW.ThetaProd.thS_mul_conj_thS : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by sorry
