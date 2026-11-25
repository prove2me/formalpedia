-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_Cutoff_gB_nonneg
-- name    : GlobalTheory.IntBall.Cutoff.gB_nonneg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:11.986247+00:00
-- url     : https://prove2.me/theorems/8c0304b5-3d4d-56de-b562-e31b66d401f4
-- title:
--   Cutoff: g B nonneg
-- statement:
--   The Cutoff construction uses the g B nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoff.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoff.lean#L25-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OfRealGramDeterminantBoundLeProdCutoff
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
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.Cutoff
noncomputable section

theorem GlobalTheory.IntBall.Cutoff.gB_nonneg {r : ℕ} (p0 : ℕ) (w : Low r → ℂ) : 0 ≤ gB p0 w := by sorry
