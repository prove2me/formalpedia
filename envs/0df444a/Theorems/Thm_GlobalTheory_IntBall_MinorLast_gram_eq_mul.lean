-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_MinorLast_gram_eq_mul
-- name    : GlobalTheory.IntBall.MinorLast.gram_eq_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:46:04.11079+00:00
-- url     : https://prove2.me/theorems/82fb8b39-3a94-4c77-9951-626f3d3f0a56
-- title:
--   Minor Last: gram eq mul
-- statement:
--   The Minor Last construction uses the gram eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundLast.lean#L80-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundLast.lean#L80-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallLeadingGramMinorLowerBoundLast
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
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.MinorLast
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ComplexOrder
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.IntBall.MinorLast.gram_eq_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by sorry
