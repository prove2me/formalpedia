-- Prove2me | Theorems.Thm_GlobalTheory_FieldModel_exists_finite_torusExtension_of_model
-- name    : GlobalTheory.FieldModel.exists_finite_torusExtension_of_model
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:32:15.933255+00:00
-- url     : https://prove2.me/theorems/4678b2ee-a5d8-434d-a2c5-65cae238afd7
-- title:
--   Field Model: exists finite torus Extension of model
-- statement:
--   The Field Model construction uses the exists finite torus Extension of model property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean#L181-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean#L181-L255

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomDescendsToSubfieldContainingFinsetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFinsetModelOfIsAffineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescendsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.FieldModel
variable {K : Type} [Field K]

theorem GlobalTheory.FieldModel.exists_finite_torusExtension_of_model {k k₀ K : Type} [Field k] [Field k₀] [Field K] {σ : k →+* K}
    {α₀ : k →+* k₀} {σ₀ : k₀ →+* K} (e₀ : σ₀.comp α₀ = σ) (G : Over (Sp k)) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsSeparated G.hom]
    (T : TorusExtension ((Over.pullback (spMap σ)).obj G)) {B₀ : Over (Sp k₀)} {φ₀ : T.B.left ⟶ B₀.left}
    (H₀ : IsPullback φ₀ T.B.hom B₀.hom (spMap σ₀)) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (ρ : k₀ →+* k₁) (β : k₁ →+* K),
      β.comp α = σ → β.comp ρ = σ₀ → ρ.comp α₀ = α →
      s ⊆ Set.range β → Nonempty (TorusExtension ((Over.pullback (spMap α)).obj G)) := by sorry
