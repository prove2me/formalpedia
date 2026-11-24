-- Prove2me | Theorems.Thm_GlobalTheory_ZMTFin_isIso_restrict_basicOpen
-- name    : GlobalTheory.ZMTFin.isIso_restrict_basicOpen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:51.436632+00:00
-- url     : https://prove2.me/theorems/9e24ed4a-d202-482a-844e-fa5ef936e57e
-- title:
--   ZMTFin: is Iso restrict basic Open
-- statement:
--   The ZMTFin construction uses the is Iso restrict basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L99-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteCompOpenImmersionOfQuasiFinite.lean#L99-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCoequifiberedSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelSpecMapIsIsoOverBasicOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapBijectiveOfRangeEqSubalgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteCompOpenImmersionOfQuasiFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
open GlobalTheory GlobalTheory.ZMTFin

theorem GlobalTheory.ZMTFin.isIso_restrict_basicOpen (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α)
    (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued)
    (hg₁ : g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase)
    (hg₂ : ∀ V, (relativeGluingData hα).cover.f V ≫ g =
      Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V)
    (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V))
    (hb : Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b))
    (W : (relativeGluingData hα').glued.Opens)
    (hW : (W : Set (relativeGluingData hα').glued) =
      (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V))))) :
    IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) =
      (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) :
        Set (PrimeSpectrum (F.obj (Opposite.op V)))) := by sorry
