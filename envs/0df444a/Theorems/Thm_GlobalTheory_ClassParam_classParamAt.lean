-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_classParamAt
-- name    : GlobalTheory.ClassParam.classParamAt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:13:38.843362+00:00
-- url     : https://prove2.me/theorems/d7571be3-9fba-41cc-ab6c-8b48c3e3882d
-- title:
--   Class Param: class Param At
-- statement:
--   The Class Param construction uses the class Param At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L788-L849
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L788-L849

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

theorem GlobalTheory.ClassParam.classParamAt [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) : ClassParamAt k hP := by sorry
