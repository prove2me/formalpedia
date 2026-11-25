-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_Cutoff_ofReal_bnd_le
-- name    : GlobalTheory.IntBall.Cutoff.ofReal_bnd_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:42.802026+00:00
-- url     : https://prove2.me/theorems/ff524ff5-8a65-429e-81b4-fd716d9dc541
-- title:
--   Cutoff: of Real bnd le
-- statement:
--   The Cutoff construction uses the of Real bnd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoff.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoff.lean#L38-L43

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.IntBall.Cutoff.ofReal_bnd_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (z : V (nd X)), z ∈ Om X → ENNReal.ofReal (bnd X z) ≤ ∏ τ, hB X.p0 (zOf X z τ) := by sorry
