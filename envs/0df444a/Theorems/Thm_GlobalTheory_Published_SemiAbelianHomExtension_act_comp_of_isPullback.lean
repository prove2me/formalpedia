-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_act_comp_of_isPullback
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.act_comp_of_isPullback
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:17:41.722579+00:00
-- url     : https://prove2.me/theorems/7d6585ce-f35f-40af-9fdb-5c753e87d477
-- title:
--   Semi Abelian Hom Extension: act comp of is Pullback
-- statement:
--   The Semi Abelian Hom Extension construction uses the act comp of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean#L147-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean#L147-L156

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
omit [AlgebraicGeometry.IsNoetherian S]

theorem GlobalTheory.Published.SemiAbelianHomExtension.act_comp_of_isPullback {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsPullback φ G'.hom G.hom j)
    {O : Type} [CommRing O] (a : OAct O G) (b : OAct O H) (a' : OAct O G') (b' : OAct O H')
    (ha : ∀ x, (a'.act x).left ≫ φ = φ ≫ (a.act x).left) (hb : ∀ x, (b'.act x).left ≫ ψ = ψ ≫ (b.act x).left)
    (f : G' ⟶ H') (hf : ∀ x, a'.act x ≫ f = f ≫ b'.act x) (F : G ⟶ H) (hF : f.left ≫ ψ = φ ≫ F.left) (x : O) :
    a.act x ≫ F = F ≫ b.act x := by sorry
