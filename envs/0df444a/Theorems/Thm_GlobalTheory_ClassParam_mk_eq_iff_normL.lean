-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_mk_eq_iff_normL
-- name    : GlobalTheory.ClassParam.mk_eq_iff_normL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:13:20.539624+00:00
-- url     : https://prove2.me/theorems/e65f8336-fdb7-4b9d-92eb-278e86c4f94f
-- title:
--   Class Param: mk eq iff norm L
-- statement:
--   The Class Param construction uses the mk eq iff norm L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L693-L700
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L693-L700

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

theorem GlobalTheory.ClassParam.mk_eq_iff_normL (hP : IsPPol c r P) (x x' : (Lplus hP ⊗[F] k)ˣ) :
    (QuotientGroup.mk x : _ ⧸ normL k hP) = QuotientGroup.mk x' ↔
      ∃ z : (AdjoinRoot P ⊗[F] k)ˣ,
        inclPlus k hP x' = inclPlus k hP x * (z * starLk k hP z) := by sorry
