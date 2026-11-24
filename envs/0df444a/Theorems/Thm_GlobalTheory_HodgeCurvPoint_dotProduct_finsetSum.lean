-- Prove2me | Theorems.Thm_GlobalTheory_HodgeCurvPoint_dotProduct_finsetSum
-- name    : GlobalTheory.HodgeCurvPoint.dotProduct_finsetSum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:19.78184+00:00
-- url     : https://prove2.me/theorems/fc860771-3418-41f1-97c6-957742b47b7e
-- title:
--   Hodge Curv Point: dot Product finset Sum
-- statement:
--   The Hodge Curv Point construction uses the dot Product finset Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L56-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}

theorem GlobalTheory.HodgeCurvPoint.dotProduct_finsetSum {a : ℕ} (u : Fin g → ℂ) (w : Fin a → Fin g → ℂ) :
    u ⬝ᵥ ∑ i, w i = ∑ i, u ⬝ᵥ w i := by sorry
