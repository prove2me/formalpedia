-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_gtExt_iota
-- name    : GlobalTheory.TorusExt.gtExt_iota
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:49.627862+00:00
-- url     : https://prove2.me/theorems/2c68169f-3f55-45d9-9639-0850015600d3
-- title:
--   Torus Ext: gt Ext iota
-- statement:
--   The Torus Ext construction uses the gt Ext iota property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L371-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L371-L374

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

theorem GlobalTheory.TorusExt.gtExt_iota (hB : D.TauBimult) (x : D.X) : gtExt D f hf (iota hB F x) = iota hB F' x := by sorry
