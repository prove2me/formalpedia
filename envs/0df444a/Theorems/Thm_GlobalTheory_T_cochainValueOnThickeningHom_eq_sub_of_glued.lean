-- Prove2me | Theorems.Thm_GlobalTheory_T_cochainValueOnThickeningHom_eq_sub_of_glued
-- name    : GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:26.811358+00:00
-- url     : https://prove2.me/theorems/d91fd640-f75f-4683-9a9c-a4f1c389dd53
-- title:
--   T: cochain Value On Thickening Hom eq sub of glued
-- statement:
--   The T construction uses the cochain Value On Thickening Hom eq sub of glued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGluedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CochainValueOnThickeningHomEqSubOfGluedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGlued
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecPullA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CochainValueOnThickeningHomEqSubOfGluedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cochainValueOnThickeningHom_eq_sub_of_glued : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 ((IsTriv s).ι ⋙ O (dp0 R) s)) (g : C0 (OAff s)), (∀ ⦃U V : AffOp X⦄ (a : U ⟶ V), g V - Sec.res s (leOfHom a.unop) (g U) = fv f ((affF s).map a)) → ∀ {T T' : TT s} (φ : T ⟶ T') (G : T.obj.B) (G' : T'.obj.B), (∀ p : Pair (pt T), toSec R T.obj.B p.1.1 G = hSec f g T p) → (∀ p : Pair (pt T'), toSec R T'.obj.B p.1.1 G' = hSec f g T' p) → fv f φ = G' - φ.hom.φ G := by sorry
