-- Prove2me | Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_matrix_mul
-- name    : GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:53.746348+00:00
-- url     : https://prove2.me/theorems/dbd97920-fc73-4b20-9c75-5c945b13e3da
-- title:
--   Torsion Holomorphic: differentiable On matrix mul
-- statement:
--   The Torsion Holomorphic construction uses the differentiable On matrix mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L43-L48

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

theorem GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul {n : Type} [Fintype n] (A B : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hB : ∀ p q, DifferentiableOn ℂ (fun e => B e p q) W) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e * B e) p q) W := by sorry
