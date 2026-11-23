-- Prove2me | Theorems.Thm_GlobalTheory_TorsionHolomorphic_differentiableOn_det
-- name    : GlobalTheory.TorsionHolomorphic.differentiableOn_det
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:41.273565+00:00
-- url     : https://prove2.me/theorems/46abca7b-0083-488c-878a-8669bde82b3d
-- title:
--   Torsion Holomorphic: differentiable On det
-- statement:
--   The Torsion Holomorphic construction uses the differentiable On det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L29-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsDifferentiableOnTorsSq.lean#L29-L40

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

theorem GlobalTheory.TorsionHolomorphic.differentiableOn_det {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W) :
    DifferentiableOn ℂ (fun e => (A e).det) W := by sorry
