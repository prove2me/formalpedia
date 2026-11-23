-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_fixed_tensor
-- name    : GlobalTheory.ClassParam.fixed_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:45.983482+00:00
-- url     : https://prove2.me/theorems/445cbdd4-ed76-4d20-83e7-c86bdcbbd0ef
-- title:
--   Class Param: fixed tensor
-- statement:
--   The Class Param construction uses the fixed tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L654-L660
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L654-L660

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
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

theorem GlobalTheory.ClassParam.fixed_tensor {W V : Type} [AddCommGroup W] [AddCommGroup V] [Module F W] [Module F V]
    (i : W →ₗ[F] V) (s : V →ₗ[F] V) (h : ∀ v, s v = v ↔ ∃ w, i w = v) (z : V ⊗[F] k) :
    s.rTensor k z = z ↔ ∃ w, i.rTensor k w = z := by sorry
