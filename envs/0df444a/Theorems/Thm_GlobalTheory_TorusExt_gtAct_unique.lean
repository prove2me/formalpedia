-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_gtAct_unique
-- name    : GlobalTheory.TorusExt.gtAct_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:31.48752+00:00
-- url     : https://prove2.me/theorems/cdc622e0-9b0d-4994-b58e-5f7aeb2291ae
-- title:
--   Torus Ext: gt Act unique
-- statement:
--   The Torus Ext construction uses the gt Act unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L169-L173

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

theorem GlobalTheory.TorusExt.gtAct_unique (hG : GlobalFnsSt) {oa : D.OAct O} {a : O} {g h h' : GtPtF D F} (e : GtAct oa a g h)
    (e' : GtAct oa a g h') : h = h' := by sorry
