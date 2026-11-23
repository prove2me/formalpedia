-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_trace_tmul_one
-- name    : GlobalTheory.ClassParam.trace_tmul_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:41.024481+00:00
-- url     : https://prove2.me/theorems/8db32b48-1434-4dbd-bfdb-df52f5d8f894
-- title:
--   Class Param: trace tmul one
-- statement:
--   The Class Param construction uses the trace tmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L585-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L585-L591

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

theorem GlobalTheory.ClassParam.trace_tmul_one {ι : Type} [Fintype ι] (b : Module.Basis ι E (AdjoinRoot P))
    (l : AdjoinRoot P) : Algebra.trace (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) (l ⊗ₜ 1)
      = Algebra.trace E (AdjoinRoot P) l ⊗ₜ 1 := by sorry
