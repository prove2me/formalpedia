-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_det_eq_prod_fibres
-- name    : GlobalTheory.DiscrJacobianBlocks.det_eq_prod_fibres
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:37.753066+00:00
-- url     : https://prove2.me/theorems/7a262949-b3b6-40f3-96de-98ffcc35096f
-- title:
--   Discr Jacobian Blocks: det eq prod fibres
-- statement:
--   The Discr Jacobian Blocks construction uses the det eq prod fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L17-L25

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

theorem GlobalTheory.DiscrJacobianBlocks.det_eq_prod_fibres {O Y : Type} [CommRing O] [DecidableEq Y] {d : ℕ} (p : Fin d → Y)
    (M : Matrix (Fin d) (Fin d) O) (hM : ∀ a a', p a ≠ p a' → M a a' = 0) :
    M.det = ∏ y ∈ Finset.univ.image p,
      (Matrix.of fun a a' : {a // p a = y} => M a.1 a'.1).det := by sorry
