-- Prove2me | Theorems.Thm_GlobalTheory_FlagGram_cube_cbrt
-- name    : GlobalTheory.FlagGram.cube_cbrt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:42:47.985358+00:00
-- url     : https://prove2.me/theorems/58080f08-3a02-484f-9371-53da8748c82e
-- title:
--   Flag Gram: cube cbrt
-- statement:
--   The Flag Gram construction uses the cube cbrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagGramDensityInequalityComplex.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FlagGramDensityInequalityComplex.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagGramDensityInequalityComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.FlagGram

theorem GlobalTheory.FlagGram.cube_cbrt (t : ℝ) (ht : 0 ≤ t) : (t ^ (1/3:ℝ)) ^ 3 = t := by sorry
