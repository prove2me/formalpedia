-- Prove2me | Theorems.Thm_GlobalTheory_Published_SemiAbelianHomExtension_model_int
-- name    : GlobalTheory.Published.SemiAbelianHomExtension.model_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:18:14.766989+00:00
-- url     : https://prove2.me/theorems/f5f81125-8ec0-45d3-acba-e59e40858518
-- title:
--   Semi Abelian Hom Extension: model int
-- statement:
--   The Semi Abelian Hom Extension construction uses the model int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean#L299-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/SemiabelianTori/GeometricallyConnectedSplitTorusAff.lean#L299-L319

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
open scoped TensorProduct

theorem GlobalTheory.Published.SemiAbelianHomExtension.model_int : AlgebraicGeometry.IsNoetherian (Sp ℤ) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp ℤ) ∧
    ∃ U : (Sp ℤ).Opens, Dense (U : Set (Sp ℤ)) ∧ U ≠ ⊤ ∧ IsSemiAbelian (Gm (Sp ℤ)) ∧
      Nontrivial (𝟙_ (Over (Sp ℤ)) ⟶ Gm (Sp ℤ)) ∧
      ∀ F₀ : Gm (Sp ℤ) ⟶ Gm (Sp ℤ), IsMonHom F₀ → IsMonHom ((Over.pullback U.ι).map F₀) ∧
        ∃! F : Gm (Sp ℤ) ⟶ Gm (Sp ℤ), IsMonHom F ∧ (Over.pullback U.ι).map F = (Over.pullback U.ι).map F₀ := by sorry
