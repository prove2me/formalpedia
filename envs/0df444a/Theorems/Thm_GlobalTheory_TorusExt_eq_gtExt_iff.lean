-- Prove2me | Theorems.Thm_GlobalTheory_TorusExt_eq_gtExt_iff
-- name    : GlobalTheory.TorusExt.eq_gtExt_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:19:28.546324+00:00
-- url     : https://prove2.me/theorems/32dd0dfa-9a82-4b71-a9f6-0d2dcabdf1d0
-- title:
--   Torus Ext: eq gt Ext iff
-- statement:
--   The Torus Ext construction uses the eq gt Ext iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L358-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/GtActIffEqGtSmul.lean#L358-L369

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

theorem GlobalTheory.TorusExt.eq_gtExt_iff (g : GtPtF D F) (g' : GtPtF D F') : g' = gtExt D f hf g ↔ g'.b.left = spMap f ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) (spMap f)) := by sorry
