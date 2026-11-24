-- Prove2me | Theorems.Thm_GlobalTheory_TensHead_piOp_tprod_update
-- name    : GlobalTheory.TensHead.piOp_tprod_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:55.023159+00:00
-- url     : https://prove2.me/theorems/a61ef92c-e5c0-483f-b138-288917357896
-- title:
--   Tens Head: pi Op tprod update
-- statement:
--   The Tens Head construction uses the pi Op tprod update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqTopOfPureTensorsOfFactorGenerators.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EqTopOfPureTensorsOfFactorGenerators.lean#L24-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
open scoped TensorProduct

theorem GlobalTheory.TensHead.piOp_tprod_update {ι : Type} [DecidableEq ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι) (g : Module.End ℂ (M i))
    (y : ∀ j, M j) (x : M i) :
    _root_.GlobalTheory.TensHead.piOp i g (PiTensorProduct.tprod ℂ (Function.update y i x)) =
      PiTensorProduct.tprod ℂ (Function.update y i (g x)) := by sorry
