-- Prove2me | Theorems.Thm_GlobalTheory_FieldModel_exists_finite_torusExtension_range
-- name    : GlobalTheory.FieldModel.exists_finite_torusExtension_range
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:55.360901+00:00
-- url     : https://prove2.me/theorems/1b24ac71-a978-488d-b894-ae1fc7241005
-- title:
--   Field Model: exists finite torus Extension range
-- statement:
--   The Field Model construction uses the exists finite torus Extension range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean#L257-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean#L257-L275

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

theorem GlobalTheory.FieldModel.exists_finite_torusExtension_range {k K : Type} [Field k] [Field K] (σ : k →+* K) (G : Over (Sp k))
    [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [IsSeparated G.hom]
    (T : TorusExtension ((Over.pullback (spMap σ)).obj G)) :
    ∃ s : Set K, s.Finite ∧ ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ →
      s ⊆ Set.range β → Nonempty (TorusExtension ((Over.pullback (spMap α)).obj G)) := by sorry
