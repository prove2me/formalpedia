-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_trLk_eq
-- name    : GlobalTheory.ClassParam.trLk_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:40.526924+00:00
-- url     : https://prove2.me/theorems/f241f3c7-9c75-495f-8dac-02a9733f28f1
-- title:
--   Class Param: tr Lk eq
-- statement:
--   The Class Param construction uses the tr Lk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L593-L599
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L593-L599

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

theorem GlobalTheory.ClassParam.trLk_eq {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P))
    (y : AdjoinRoot P ⊗[F] k) : trLk k P y = Algebra.trace (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) y := by sorry
