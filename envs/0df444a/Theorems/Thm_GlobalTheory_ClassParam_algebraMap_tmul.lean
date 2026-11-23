-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_algebraMap_tmul
-- name    : GlobalTheory.ClassParam.algebraMap_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:57.840403+00:00
-- url     : https://prove2.me/theorems/9b043f7d-9ad5-4211-8b32-a4e1bd931c55
-- title:
--   Class Param: algebra Map tmul
-- statement:
--   The Class Param construction uses the algebra Map tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L541-L542
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L541-L542

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

theorem GlobalTheory.ClassParam.algebraMap_tmul (e : E) (t : k) :
    algebraMap (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) (e ⊗ₜ t) = AdjoinRoot.of P e ⊗ₜ t := by sorry
