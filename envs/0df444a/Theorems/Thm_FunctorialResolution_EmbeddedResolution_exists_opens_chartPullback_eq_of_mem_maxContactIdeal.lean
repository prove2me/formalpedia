-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_opens_chartPullback_eq_of_mem_maxContactIdeal
-- name    : FunctorialResolution.EmbeddedResolution.exists_opens_chartPullback_eq_of_mem_maxContactIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:54:07.849879+00:00
-- url     : https://prove2.me/theorems/d2cc399f-299f-4202-aed2-97b13f4b097f
-- title:
--   Embedded Resolution: exists opens chart Pullback eq of mem max Contact Ideal
-- statement:
--   The Embedded Resolution construction uses the exists opens chart Pullback eq of mem max Contact Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactChartUniqueness.lean#L774-L862
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/MaximalContactHypersurfaces/MaxContactChartUniqueness.lean#L774-L862

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansionComparison
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_StalkIdealSpreadOut
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_MaxContactChartUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.exists_opens_chartPullback_eq_of_mem_maxContactIdeal
    (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hinv : IsMaxContactInvariant k p I m)
    {U : X.Opens} (hU : IsAffineOpen U) {n : ℕ} (c₁ c₂ : EtaleChart p U n) (j : Fin n)
    (hcoord : ∀ i : Fin n, i ≠ j → c₁.coord i = c₂.coord i)
    (x : X) (hx : x ∈ U)
    (hmem₁ : c₁.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hmem₂ : c₂.coord j ∈ (maxContactIdeal k p I m).ideal ⟨U, hU⟩)
    (hg₁ : (X.presheaf.germ U x hx).hom (c₁.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hg₂ : (X.presheaf.germ U x hx).hom (c₂.coord j) ∈
      IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
    (hsupp : x ∈ (maxContactIdeal k p I m).support)
    [IsLocallyNoetherian (chartPullback c₁ c₂)]
    [IsLocallyNoetherian ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subscheme] :
    ∃ h : ChartsAgreeAt c₁ c₂ x hx,
      ∃ W : (chartPullback c₁ c₂).Opens, chartPullbackPoint c₁ c₂ x hx h ∈ W ∧
        (∀ y : ↥(chartPullback c₁ c₂), y ∈ W →
            stalkIdeal (I.comap (chartPullbackFst c₁ c₂)) y =
              stalkIdeal (I.comap (chartPullbackSnd c₁ c₂)) y) ∧
        restrictIdeal (I.comap (chartPullbackFst c₁ c₂)) W =
          restrictIdeal (I.comap (chartPullbackSnd c₁ c₂)) W ∧
        ((((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
                chartPullbackFst c₁ c₂ =
            (((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ⁻¹ᵁ W).ι ≫
              ((maxContactIdeal k p I m).comap (chartPullbackFst c₁ c₂)).subschemeι ≫
                chartPullbackSnd c₁ c₂) ∧
        ((c₁.coordIdeal {j}).comap (pullback.fst c₁.map c₂.map) =
          (c₂.coordIdeal {j}).comap (pullback.snd c₁.map c₂.map)) ∧
        ∀ S : Finset (Fin n), j ∉ S → c₁.coordIdeal S = c₂.coordIdeal S := by sorry
