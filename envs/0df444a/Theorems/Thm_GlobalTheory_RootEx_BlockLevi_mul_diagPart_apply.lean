-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_BlockLevi_mul_diagPart_apply
-- name    : GlobalTheory.RootEx.BlockLevi.mul_diagPart_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:55.153826+00:00
-- url     : https://prove2.me/theorems/a5b64a8e-9a84-475a-b186-32e70a4693af
-- title:
--   Block Levi: mul diag Part apply
-- statement:
--   The Block Levi construction uses the mul diag Part apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean#L12-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.BlockLevi
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.RootEx.BlockLevi.mul_diagPart_apply (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) {r s : ι} (h : f s ≤ f r) :
    (A * diagPart f B) r s = (A * B) r s := by sorry
