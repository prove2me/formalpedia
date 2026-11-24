-- Prove2me | Theorems.Thm_GlobalTheory_T_relSpec_map_isIso_over_basicOpen_alt
-- name    : GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:21.470838+00:00
-- url     : https://prove2.me/theorems/72ef4764-e44b-41ba-90f7-3041a6dea0d8
-- title:
--   T: rel Spec map is Iso over basic Open alt
-- statement:
--   The T construction uses the rel Spec map is Iso over basic Open alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelSpecMapIsIsoOverBasicOpenStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelSpecMapIsIsoOverBasicOpenStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpen
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt : ∀ (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat) (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F), α' ≫ ι = α → ∀ (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued), g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase → (∀ V, (relativeGluingData hα).cover.f V ≫ g = Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V) → ∀ (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V)), Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b) → ∀ (W : (relativeGluingData hα').glued.Opens), (W : Set (relativeGluingData hα').glued) = (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V)))) → IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) = (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) : Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by sorry
