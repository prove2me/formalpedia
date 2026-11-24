-- Prove2me | Theorems.Thm_GlobalTheory_IdealChain_smul_frame_mul_frame_inv_apply
-- name    : GlobalTheory.IdealChain.smul_frame_mul_frame_inv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:01.526732+00:00
-- url     : https://prove2.me/theorems/6d8cf360-a698-4b1f-a081-2062ab78ab8b
-- title:
--   Ideal Chain: smul frame mul frame inv apply
-- statement:
--   The Ideal Chain construction uses the smul frame mul frame inv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmulFrameMulFrameInvApply.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmulFrameMulFrameInvApply.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarMeasurePiChangeConstantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
open GlobalTheory GlobalTheory.IdealChain

theorem GlobalTheory.IdealChain.smul_frame_mul_frame_inv_apply {k : Type} [Field k]
    {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c c' : ℕ} (a : k) (b b' : ℕ → kˣ)
    (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin c') k) (r : n ⊕ Fin c) (s : n' ⊕ Fin c') :
    (a • ((frame n c b).val * y * ((frame n' c' b')⁻¹).val)) r s =
      a * Sum.elim (fun _ : n => (1 : k)) (fun i : Fin c => (b (i.val + 1) : k)) r *
        Sum.elim (fun _ : n' => (1 : k)) (fun i : Fin c' => (b' (i.val + 1) : k)⁻¹) s * y r s := by sorry
