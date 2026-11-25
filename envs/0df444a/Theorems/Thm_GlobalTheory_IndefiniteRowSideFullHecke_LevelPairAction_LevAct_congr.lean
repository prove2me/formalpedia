-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LevelPairAction_LevAct_congr
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction.LevAct.congr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:10:13.89124+00:00
-- url     : https://prove2.me/theorems/0c1b9013-a6d4-5c5f-834e-33c170f32222
-- title:
--   Lev Act: congr
-- statement:
--   The Lev Act construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelPairAction.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LevelPairAction.lean#L76-L86

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelPairAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction.LevAct.congr {gM gM' gA gA' : Dw.La →ₗ[𝓞 E] Dw.La} (hM : CongM l gM' gM) (hA : CongN l.A gA' gA)
    {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : LevAct gM gA y y') : LevAct gM' gA' y y' := by sorry
