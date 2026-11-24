-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_diagGL_val
-- name    : GlobalTheory.DetFactor.diagGL_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:28.587684+00:00
-- url     : https://prove2.me/theorems/ebde7bf0-91e1-4370-a86e-bbfe6e013045
-- title:
--   Det Factor: diag GL val
-- statement:
--   The Det Factor construction uses the diag GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L14-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L14-L14

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

theorem GlobalTheory.DetFactor.diagGL_val {n : ℕ} (d : Fin n → kˣ) : ((diagGL n d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) := by sorry
