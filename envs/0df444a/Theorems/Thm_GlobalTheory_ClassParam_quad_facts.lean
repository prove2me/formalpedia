-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_quad_facts
-- name    : GlobalTheory.ClassParam.quad_facts
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:13:30.213303+00:00
-- url     : https://prove2.me/theorems/96fbbbaa-385f-4076-9c6f-8fc05081b408
-- title:
--   Class Param: quad facts
-- statement:
--   The Class Param construction uses the quad facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L886-L898
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L886-L898

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

theorem GlobalTheory.ClassParam.quad_facts [CharZero F] (h2 : Module.finrank F E = 2) (hc1 : c ≠ 1) :
    (∀ e, c (c e) = e) ∧ ∀ e, c e = e → ∃ a, algebraMap F E a = e := by sorry
