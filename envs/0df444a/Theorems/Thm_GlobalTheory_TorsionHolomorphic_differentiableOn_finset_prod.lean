-- Prove2me | Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_finset_prod
-- name    : GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:40.454892+00:00
-- url     : https://prove2.me/theorems/9a16343d-4f42-46a6-b6ff-85fa7cf4df98
-- title:
--   Torsion Holomorphic: differentiable On finset prod
-- statement:
--   The Torsion Holomorphic construction uses the differentiable On finset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L10-L19

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

theorem GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∏ i ∈ s, f i e) W := by sorry
