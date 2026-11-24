-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_pt_comp
-- name    : GlobalTheory.CechDR.AffLoc.pt_comp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:14:46.911329+00:00
-- url     : https://prove2.me/theorems/e4713308-9ba3-42bc-b9c4-b2cc40d5115d
-- title:
--   Aff Loc: pt comp
-- statement:
--   The Aff Loc construction uses the pt comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean#L18-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecFunctionsEqOfRestrictionsOnPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem GlobalTheory.CechDR.AffLoc.pt_comp {T T' : TT s} (φ : T ⟶ T') :
    pt T' = spMap (φ.hom.φ : T.obj.B →+* T'.obj.B) ≫ pt T := by sorry
