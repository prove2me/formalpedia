-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_gtExt_gtSmul
-- name    : GlobalTheory.TorusExt.gtExt_gtSmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:20:07.194493+00:00
-- url     : https://prove2.me/theorems/cc6d8a20-7998-4695-8a3d-ee8fa883f80d
-- title:
--   Torus Ext: gt Ext gt Smul
-- statement:
--   The Torus Ext construction uses the gt Ext gt Smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L376-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L376-L381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_GtActIffEqGtSmul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']
variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem GlobalTheory.TorusExt.gtExt_gtSmul {O : Type} [CommRing O] [StarRing O] [Module O D.X] (hG : GlobalFnsSt) (oa : D.OAct O) (a : O)
    (g : GtPtF D F) : gtExt D f hf (gtSmul hG oa a g) = gtSmul hG oa a (gtExt D f hf g) := by sorry
