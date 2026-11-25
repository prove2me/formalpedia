-- Prove2me | Theorems.Thm_GlobalTheory_IntBallMinorOne_gram_mul_right
-- name    : GlobalTheory.IntBallMinorOne.gram_mul_right
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:45:40.899884+00:00
-- url     : https://prove2.me/theorems/0e749566-3d5c-4928-b773-bcbf0f46c1f1
-- title:
--   Int Ball Minor One: gram mul right
-- statement:
--   The Int Ball Minor One construction uses the gram mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundFirst.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundFirst.lean#L172-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBallMinorOne
open Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.IntBallMinorOne.gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by sorry
