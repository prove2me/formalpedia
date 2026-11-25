-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_gtAct_iff_eq_gtSmul
-- name    : GlobalTheory.TorusExt.gtAct_iff_eq_gtSmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:35.028133+00:00
-- url     : https://prove2.me/theorems/04179298-6a49-4614-8c5e-fc223ef97800
-- title:
--   Torus Ext: gt Act iff eq gt Smul
-- statement:
--   The Torus Ext construction uses the gt Act iff eq gt Smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L225-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L225-L226

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorusExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
attribute [local instance] gtGroup
variable {O : Type} [CommRing O] [StarRing O] [Module O D.X]
variable (hG : GlobalFnsSt) (oa : D.OAct O)

theorem GlobalTheory.TorusExt.gtAct_iff_eq_gtSmul (a : O) (g g' : GtPtF D F) : GtAct oa a g g' ↔ g' = gtSmul hG oa a g := by sorry
