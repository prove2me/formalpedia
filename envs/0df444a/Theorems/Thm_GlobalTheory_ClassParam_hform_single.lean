-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_hform_single
-- name    : GlobalTheory.ClassParam.hform_single
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:50.477516+00:00
-- url     : https://prove2.me/theorems/da48fc59-4828-40de-9d36-9b1c17208779
-- title:
--   Class Param: hform single
-- statement:
--   The Class Param construction uses the hform single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L168-L170

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

theorem GlobalTheory.ClassParam.hform_single (J : Matrix (Fin r) (Fin r) A) (i j : Fin r) :
    hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by sorry
