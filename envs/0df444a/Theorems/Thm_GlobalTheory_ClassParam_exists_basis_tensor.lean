-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_exists_basis_tensor
-- name    : GlobalTheory.ClassParam.exists_basis_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:05.769329+00:00
-- url     : https://prove2.me/theorems/82c61e3d-4d69-48c3-8af6-da1d2b27fe5c
-- title:
--   Class Param: exists basis tensor
-- statement:
--   The Class Param construction uses the exists basis tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L559-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L559-L583

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

theorem GlobalTheory.ClassParam.exists_basis_tensor {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P)) :
    ∃ b' : Module.Basis ι (E ⊗[F] k) (AdjoinRoot P ⊗[F] k), ∀ i, b' i = b i ⊗ₜ 1 := by sorry
