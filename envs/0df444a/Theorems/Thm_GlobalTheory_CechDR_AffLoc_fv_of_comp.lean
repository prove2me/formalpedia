-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_fv_of_comp
-- name    : GlobalTheory.CechDR.AffLoc.fv_of_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:14:07.465588+00:00
-- url     : https://prove2.me/theorems/ba5ebae7-19da-4742-a7ae-dc7c1d43292e
-- title:
--   Aff Loc: fv of comp
-- statement:
--   The Aff Loc construction uses the fv of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean#L29-L34

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

theorem GlobalTheory.CechDR.AffLoc.fv_of_comp (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) {T₁ T₂ T₃ : TT s} (a : T₁ ⟶ T₂)
    (c : T₂ ⟶ T₃) (d : T₁ ⟶ T₃) (h : ∀ x, c.hom.φ (a.hom.φ x) = d.hom.φ x) :
    fv f d = c.hom.φ (fv f a) + fv f c := by sorry
