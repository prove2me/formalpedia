-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_hform_symm
-- name    : GlobalTheory.ClassParam.hform_symm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:48.810894+00:00
-- url     : https://prove2.me/theorems/e1a84c8a-34c5-40d1-9727-fb8f551809a4
-- title:
--   Class Param: hform symm
-- statement:
--   The Class Param construction uses the hform symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L190-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L190-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
variable {A : Type} [CommRing A] {r : ℕ} (σ : A →+* A)

theorem GlobalTheory.ClassParam.hform_symm (hσ : ∀ a, σ (σ a) = a) {J : Matrix (Fin r) (Fin r) A} (hJ : IsHerm σ J)
    (x y : Fin r → A) : hform σ J y x = σ (hform σ J x y) := by sorry
