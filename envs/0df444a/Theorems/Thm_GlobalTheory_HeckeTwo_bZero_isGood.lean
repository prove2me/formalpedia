-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwo_bZero_isGood
-- name    : GlobalTheory.HeckeTwo.bZero_isGood
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:07:11.85353+00:00
-- url     : https://prove2.me/theorems/8fb80a9c-66a1-4b06-97ba-dcb72e48d0d4
-- title:
--   Hecke Two: b Zero is Good
-- statement:
--   The Hecke Two construction uses the b Zero is Good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic.lean#L34-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic.lean#L34-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwo
open GlobalTheory.HeckeTwo.BZeroGood

theorem GlobalTheory.HeckeTwo.bZero_isGood (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (hf : 2 ≤ Module.finrank ℚ F)
    (𝔞 𝔟 : Frac F) (Zb R : ℂ → ℂ) (hR : Differentiable ℂ R) (hZ : ∀ s : ℂ, s ≠ 1 → Zb s = R s / (s - 1)) :
    IsGood (bZero Zb 𝔞 𝔟) := by sorry
