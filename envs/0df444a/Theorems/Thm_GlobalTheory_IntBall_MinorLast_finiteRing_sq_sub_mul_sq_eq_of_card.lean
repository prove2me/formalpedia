-- Prove2me | Theorems.Thm_GlobalTheory_IntBall_MinorLast_finiteRing_sq_sub_mul_sq_eq_of_card
-- name    : GlobalTheory.IntBall.MinorLast.finiteRing_sq_sub_mul_sq_eq_of_card
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:47:33.387151+00:00
-- url     : https://prove2.me/theorems/05b702d8-a18f-59f8-9afd-9265c84d77a1
-- title:
--   Minor Last: finite Ring sq sub mul sq eq of card
-- statement:
--   The Minor Last construction uses the finite Ring sq sub mul sq eq of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundLast.lean#L134-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitBallLeadingGramMinorLowerBoundLast.lean#L134-L199

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ}

theorem GlobalTheory.IntBall.MinorLast.finiteRing_sq_sub_mul_sq_eq_of_card (X : Data E (p + 1)) (hp : X.p0 = p) (x0 : Base X) (z : V (nd X)) (τ : X.Ψ)
    (k : Fin p) :
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.succ ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by sorry
