-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_exists_UJ
-- name    : GlobalTheory.ClassParam.exists_UJ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:21.011812+00:00
-- url     : https://prove2.me/theorems/f5d9b2d0-ccb1-4e98-b53c-7e0a8c676ec3
-- title:
--   Class Param: exists UJ
-- statement:
--   The Class Param construction uses the exists UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L181-L188

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

theorem GlobalTheory.ClassParam.exists_UJ (J : Matrix (Fin r) (Fin r) A) (t : (Fin r → A) ≃ₗ[A] (Fin r → A))
    (ht : ∀ x y, hform σ J (t x) (t y) = hform σ J x y) :
    ∃ g : UJ σ J, ∀ u, ((g : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) *ᵥ u = t u := by sorry
