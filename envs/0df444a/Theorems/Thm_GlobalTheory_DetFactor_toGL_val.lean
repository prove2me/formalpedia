-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_toGL_val
-- name    : GlobalTheory.DetFactor.toGL_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:21.643807+00:00
-- url     : https://prove2.me/theorems/abb6e71c-5afd-4e95-894c-974579ca7c31
-- title:
--   Det Factor: to GL val
-- statement:
--   The Det Factor construction uses the to GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L19-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}

theorem GlobalTheory.DetFactor.toGL_val {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M := by sorry

attribute [defeq] GlobalTheory.DetFactor.toGL_val
