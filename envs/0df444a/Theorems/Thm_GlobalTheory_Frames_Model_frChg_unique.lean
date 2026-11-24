-- Prove2me | Theorems.Thm_GlobalTheory_Frames_Model_frChg_unique
-- name    : GlobalTheory.Frames.Model.frChg_unique
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:40:55.646801+00:00
-- url     : https://prove2.me/theorems/3700e3f2-2d74-4ac9-a425-167c5892b28a
-- title:
--   Model: fr Chg unique
-- statement:
--   The Model construction uses the fr Chg unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L281-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ExistenceOfLattices/FrameRingGlRing.lean#L281-L288

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

theorem GlobalTheory.Frames.Model.frChg_unique {S : Type} [CommRing S] [Algebra c.F S]
    {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a a' : S} {y y' : FrPt Xo c S}
    (h : FrChg g a y y') (h' : FrChg g' a' y y') : g = g' ∧ a = a' := by sorry
