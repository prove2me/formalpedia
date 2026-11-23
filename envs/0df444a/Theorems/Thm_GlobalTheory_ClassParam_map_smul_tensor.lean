-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_map_smul_tensor
-- name    : GlobalTheory.ClassParam.map_smul_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:54.693529+00:00
-- url     : https://prove2.me/theorems/d8376310-25e9-4921-8594-db3fb14cc120
-- title:
--   Class Param: map smul tensor
-- statement:
--   The Class Param construction uses the map smul tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L544-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L544-L557

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

theorem GlobalTheory.ClassParam.map_smul_tensor (f : AdjoinRoot P →ₗ[E] E) (a : E ⊗[F] k) (y : AdjoinRoot P ⊗[F] k) :
    TensorProduct.map (f.restrictScalars F) LinearMap.id (a • y)
      = a * TensorProduct.map (f.restrictScalars F) LinearMap.id y := by sorry
