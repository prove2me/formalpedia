-- Prove2me | Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_finset_sum
-- name    : GlobalTheory.TorsionHolomorphic.differentiableOn_finset_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:32.034634+00:00
-- url     : https://prove2.me/theorems/2825a887-3988-5b86-87eb-519ca878195a
-- title:
--   Torsion Holomorphic: differentiable On finset sum
-- statement:
--   The Torsion Holomorphic construction uses the differentiable On finset sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L22-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsDifferentiableOnTorsSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionHolomorphic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.TorsionHolomorphic.differentiableOn_finset_sum {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∑ i ∈ s, f i e) W := by sorry
