-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_Cutoff_zOf_mem_cut
-- name    : GlobalTheory.IntBall.Cutoff.zOf_mem_cut
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:45:36.349846+00:00
-- url     : https://prove2.me/theorems/3cc900b6-eaef-457b-ac21-7834ecc96fc5
-- title:
--   Cutoff: z Of mem cut
-- statement:
--   The Cutoff construction uses the z Of mem cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoff.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OfRealGramDeterminantBoundLeProdCutoff.lean#L30-L36

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

theorem GlobalTheory.IntBall.Cutoff.zOf_mem_cut (X : Data E r) {z : V (nd X)} (hz : z ∈ Om X) (τ : X.Ψ) :
    zOf X z τ ∈ {w : Low r → ℂ | ∀ p : Low r, (p.1.2 : ℕ) < X.p0 → X.p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} := by sorry
