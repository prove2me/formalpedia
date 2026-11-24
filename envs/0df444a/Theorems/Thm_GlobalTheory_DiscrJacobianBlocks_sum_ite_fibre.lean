-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_sum_ite_fibre
-- name    : GlobalTheory.DiscrJacobianBlocks.sum_ite_fibre
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:50:37.911857+00:00
-- url     : https://prove2.me/theorems/8399d141-ae56-4c2b-bdf4-118310f912d7
-- title:
--   Discr Jacobian Blocks: sum ite fibre
-- statement:
--   The Discr Jacobian Blocks construction uses the sum ite fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L27-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks

theorem GlobalTheory.DiscrJacobianBlocks.sum_ite_fibre {M Y : Type} [AddCommMonoid M] [DecidableEq Y] {d : ℕ} (p : Fin d → Y)
    (y : Y) (f : Fin d → M) :
    (∑ a, if y = p a then f a else 0) = ∑ x : {a // p a = y}, f x.1 := by sorry
