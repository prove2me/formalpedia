-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_dvr_of_isGrpPullback
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.dvr_of_isGrpPullback
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:56.970806+00:00
-- url     : https://prove2.me/theorems/0b2052c0-1de1-494b-9a11-8ecdbaec8d37
-- title:
--   Semi Abelian Hom Extension: dvr of is Grp Pullback
-- statement:
--   The Semi Abelian Hom Extension construction uses the dvr of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean#L196-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean#L196-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
variable (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]
variable {T K}

theorem GlobalTheory.Published.SemiAbelianHomExtension.dvr_of_isGrpPullback (h : SemiAbelianHomExtension) {G H : Over (Sp T)} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over (Sp K)} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G (spMap (algebraMap T K)) φ)
    (hψ : IsGrpPullback H' H (spMap (algebraMap T K)) ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by sorry
