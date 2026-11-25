-- Prove2me | Theorems.Thm_GlobalTheory_GrassModel_topBig_tmul
-- name    : GlobalTheory.GrassModel.topBig_tmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:06:12.835388+00:00
-- url     : https://prove2.me/theorems/2f869adc-6831-4cce-94cf-c636aa0adce4
-- title:
--   Grass Model: top Big tmul
-- statement:
--   The Grass Model construction uses the top Big tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/VecMulVecComm.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/VecMulVecComm.lean#L46-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open GlobalTheory GlobalTheory.GrassModel
variable (n : ℕ)

theorem GlobalTheory.GrassModel.topBig_tmul (x y : Ext n) : topBig n (x ⊗ₜ y) = topExt n x * topExt n y := by sorry
