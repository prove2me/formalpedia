-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_map_diagGL_eq
-- name    : GlobalTheory.DetFactor.map_diagGL_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:13.734504+00:00
-- url     : https://prove2.me/theorems/755d4981-af25-4279-8aae-ba92bdfb5b4f
-- title:
--   Det Factor: map diag GL eq
-- statement:
--   The Det Factor construction uses the map diag GL eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L75-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L75-L87

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

theorem GlobalTheory.DetFactor.map_diagGL_eq (c : GL (Fin (m + 1)) k →* ℂˣ) (d : Fin (m + 1) → kˣ) :
    c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0) (∏ i, d i) := by sorry
