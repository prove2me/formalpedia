-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_exists_basis_plus
-- name    : GlobalTheory.ClassParam.exists_basis_plus
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:37.437393+00:00
-- url     : https://prove2.me/theorems/970a2653-237d-4f86-9856-837ab41b563c
-- title:
--   Class Param: exists basis plus
-- statement:
--   The Class Param construction uses the exists basis plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L711-L763
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L711-L763

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

theorem GlobalTheory.ClassParam.exists_basis_plus [CharZero E] (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1)
    (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) {ι : Type} [Fintype ι]
    (b : Module.Basis ι F (Lplus hP)) :
    ∃ b' : Module.Basis ι E (AdjoinRoot P), ∀ i, b' i = b i := by sorry
