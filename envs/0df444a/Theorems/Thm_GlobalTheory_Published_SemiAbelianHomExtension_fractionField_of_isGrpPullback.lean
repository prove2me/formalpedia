-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_fractionField_of_isGrpPullback
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.fractionField_of_isGrpPullback
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:16:31.580553+00:00
-- url     : https://prove2.me/theorems/40da5168-ada5-4639-b49f-7386f9b455ab
-- title:
--   Semi Abelian Hom Extension: fraction Field of is Grp Pullback
-- statement:
--   The Semi Abelian Hom Extension construction uses the fraction Field of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L585-L591
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L585-L591

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GenericExistsUniqueOActOfIsGrpPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.Published GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [IsIntegral S] [AlgebraicGeometry.IsNoetherian S] {j : U ⟶ S}

theorem GlobalTheory.Published.SemiAbelianHomExtension.fractionField_of_isGrpPullback (h : SemiAbelianHomExtension) {R K : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {G H : Over (Sp R)}
    [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over (Sp K)} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G (spMap (algebraMap R K)) φ) (hψ : IsGrpPullback H' H (spMap (algebraMap R K)) ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by sorry
