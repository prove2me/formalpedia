-- Prove2me | Theorems.Thm_GlobalTheory_T_cosine_square_pushforward_uniform
-- name    : GlobalTheory.T.cosine_square_pushforward_uniform
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:31:33.516258+00:00
-- url     : https://prove2.me/theorems/72b5d36e-4fb8-4d27-8408-7357aa249f07
-- title:
--   T: cosine square pushforward uniform
-- statement:
--   The T construction uses the cosine square pushforward uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CosineSquarePushforwardUniformStatement.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CosineSquarePushforwardUniformStatement.lean#L8-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniform
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cosine_square_pushforward_uniform : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ) (s : Bool), G.PosDef →
    Measure.map (GlobalTheory.LineCos.cosSq s G)
        (volume.withDensity fun x : ℂ => ENNReal.ofReal (G.det.re /
          (Real.pi * (GlobalTheory.LineCos.hform G (GlobalTheory.LineCos.lineVec s x) (GlobalTheory.LineCos.lineVec s x)).re ^ 2))) =
      volume.restrict (Set.Icc (0 : ℝ) 1) := by sorry
