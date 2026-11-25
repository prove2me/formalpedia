-- Prove2me | Theorems.Thm_GlobalTheory_spread_hom_generic_of_isGrpPullback
-- name    : GlobalTheory.spread_hom_generic_of_isGrpPullback
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:35.496376+00:00
-- url     : https://prove2.me/theorems/01f75c57-9679-57b2-aea4-597abb4e4b1c
-- title:
--   Global Theory: spread hom generic of is Grp Pullback
-- statement:
--   The Global Theory construction uses the spread hom generic of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L338-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GenericExistsUniqueOActOfIsGrpPullback.lean#L338-L472

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
open GlobalTheory
open ExtUnique

theorem GlobalTheory.spread_hom_generic_of_isGrpPullback {U S : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] {j : U ⟶ S}
    (hj : IsGenericPointHom j) {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [QuasiCompact G.hom]
    [QuasiSeparated G.hom] [IsSeparated H.hom] [LocallyOfFinitePresentation H.hom] {G' H' : Over U} [GrpObj G']
    [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ (V : S.Opens) (_ : genericPoint S ∈ V) (_ : IsAffineOpen V)
      (g : (Over.pullback V.ι).obj G ⟶ (Over.pullback V.ι).obj H) (_ : IsMonHom g)
      (w : G'.left ⟶ ((Over.pullback V.ι).obj G).left),
      w ≫ pullback.fst G.hom V.ι = φ ∧ w ≫ g.left ≫ pullback.fst H.hom V.ι = f.left ≫ ψ := by sorry
