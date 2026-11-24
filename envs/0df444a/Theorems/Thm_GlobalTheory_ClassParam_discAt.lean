-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_discAt
-- name    : GlobalTheory.ClassParam.discAt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:34.692797+00:00
-- url     : https://prove2.me/theorems/d26ffde7-8f46-4198-95ad-ea2d369d4e62
-- title:
--   Class Param: disc At
-- statement:
--   The Class Param construction uses the disc At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L851-L884
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L851-L884

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

theorem GlobalTheory.ClassParam.discAt [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1) (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) :
    DiscAt k hP := by sorry
