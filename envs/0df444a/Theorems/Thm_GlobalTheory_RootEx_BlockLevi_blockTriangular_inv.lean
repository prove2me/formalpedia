-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_BlockLevi_blockTriangular_inv
-- name    : GlobalTheory.RootEx.BlockLevi.blockTriangular_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:49.530811+00:00
-- url     : https://prove2.me/theorems/29859157-b863-442c-a941-c5a606d5288e
-- title:
--   Block Levi: block Triangular inv
-- statement:
--   The Block Levi construction uses the block Triangular inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean#L42-L46

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

theorem GlobalTheory.RootEx.BlockLevi.blockTriangular_inv (f : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular f) :
    (b⁻¹).val.BlockTriangular f := by sorry
