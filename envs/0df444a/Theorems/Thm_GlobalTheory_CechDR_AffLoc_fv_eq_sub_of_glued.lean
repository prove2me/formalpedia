-- Prove2me | Theorems.Thm_GlobalTheory_CechDR_AffLoc_fv_eq_sub_of_glued
-- name    : GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:14:59.344799+00:00
-- url     : https://prove2.me/theorems/b17e0e82-39ea-4277-9de6-339dc0d43671
-- title:
--   Aff Loc: fv eq sub of glued
-- statement:
--   The Aff Loc construction uses the fv eq sub of glued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean#L51-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGlued.lean#L51-L99

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

theorem GlobalTheory.CechDR.AffLoc.fv_eq_sub_of_glued : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R}
    (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)),
    (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) →
    ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B),
    (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) →
    (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) →
    fv f φ = G' - φ.hom.φ G := by sorry
