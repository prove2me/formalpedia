-- Prove2me | Theorems.Thm_GlobalTheory_LineCos_fsDensity_pos
-- name    : GlobalTheory.LineCos.fsDensity_pos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:08:04.864798+00:00
-- url     : https://prove2.me/theorems/d4747b2b-a017-41a6-9baf-9c61618070a7
-- title:
--   Line Cos: fs Density pos
-- statement:
--   The Line Cos construction uses the fs Density pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPoint.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LocalDensityBoundNearPoint.lean#L53-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos

theorem GlobalTheory.LineCos.fsDensity_pos (s : Bool) {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < fsDensity s G x := by sorry
