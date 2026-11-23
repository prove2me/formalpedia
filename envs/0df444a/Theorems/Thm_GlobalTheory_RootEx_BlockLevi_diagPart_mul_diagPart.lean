-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_BlockLevi_diagPart_mul_diagPart
-- name    : GlobalTheory.RootEx.BlockLevi.diagPart_mul_diagPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:19.878695+00:00
-- url     : https://prove2.me/theorems/34c5ffbc-d562-490d-a05c-f2a390c17393
-- title:
--   Block Levi: diag Part mul diag Part
-- statement:
--   The Block Levi construction uses the diag Part mul diag Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DiagPartMulDiagPart.lean#L23-L40

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

theorem GlobalTheory.RootEx.BlockLevi.diagPart_mul_diagPart (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) (hAB : A * B = 1) :
    diagPart f A * diagPart f B = 1 := by sorry
