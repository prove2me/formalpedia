-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_mem_UJ_iff
-- name    : GlobalTheory.ClassParam.mem_UJ_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:17.63028+00:00
-- url     : https://prove2.me/theorems/30867e0d-291c-4325-88f7-fe3b3942d15a
-- title:
--   Class Param: mem UJ iff
-- statement:
--   The Class Param construction uses the mem UJ iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L172-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L172-L179

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

theorem GlobalTheory.ClassParam.mem_UJ_iff (J : Matrix (Fin r) (Fin r) A) (g : GL (Fin r) A) :
    g ∈ UJ σ J ↔ ∀ x y, hform σ J ((g : Matrix (Fin r) (Fin r) A) *ᵥ x)
      ((g : Matrix (Fin r) (Fin r) A) *ᵥ y) = hform σ J x y := by sorry
