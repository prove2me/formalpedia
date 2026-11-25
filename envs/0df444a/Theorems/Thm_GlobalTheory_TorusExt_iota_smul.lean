-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_iota_smul
-- name    : GlobalTheory.TorusExt.iota_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:46.15645+00:00
-- url     : https://prove2.me/theorems/7964d1b0-f978-4225-a70f-994c307f4240
-- title:
--   Torus Ext: iota smul
-- statement:
--   The Torus Ext construction uses the iota smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L291-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L291-L303

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

theorem GlobalTheory.TorusExt.iota_smul (hB : D.TauBimult) (a : O) (x : D.X) : iota hB F (a • x) = gtSmul hG oa a (iota hB F x) := by sorry
