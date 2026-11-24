-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_map_transvection_eq_one
-- name    : GlobalTheory.DetFactor.map_transvection_eq_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:13.506357+00:00
-- url     : https://prove2.me/theorems/b0eab0a4-da3e-4790-a4e4-576eaafa5fa9
-- title:
--   Det Factor: map transvection eq one
-- statement:
--   The Det Factor construction uses the map transvection eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L40-L54

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

theorem GlobalTheory.DetFactor.map_transvection_eq_one (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) {i j : Fin n}
    (hij : i ≠ j) (t : k) : c (toGL (transvection i j t) (det_transvection_ne hij t)) = 1 := by sorry
