-- Prove2me | Theorems.Thm_GlobalTheory_Frames_Model_OpenChart_eq_lift
-- name    : GlobalTheory.Frames.Model.OpenChart.eq_lift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:06:43.218363+00:00
-- url     : https://prove2.me/theorems/9236d867-c6cb-5607-8601-79cd7aa7d414
-- title:
--   Open Chart: eq lift
-- statement:
--   The Open Chart construction uses the eq lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L329-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L329-L337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.Frames.Model.OpenChart.eq_lift {R : Type} [CommRing R] [Algebra c.F R] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R}
    (h : OpenChart j y₀) :
    j = pullback.lift y₀.x (spMap (algebraMap c.F R)) (by rw [y₀.x_over, sOf]; simp [spMap]) := by sorry
