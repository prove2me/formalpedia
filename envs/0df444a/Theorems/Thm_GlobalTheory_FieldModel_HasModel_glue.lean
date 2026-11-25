-- Prove2me | Theorems.Thm_GlobalTheory_FieldModel_HasModel_glue
-- name    : GlobalTheory.FieldModel.HasModel.glue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:19.435253+00:00
-- url     : https://prove2.me/theorems/2d6dc2bb-1ca5-4d39-9e92-a93a25133f64
-- title:
--   Has Model: glue
-- statement:
--   The Has Model construction uses the glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean#L47-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFiniteTorusExtensionOfModel.lean#L47-L72

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

theorem GlobalTheory.FieldModel.HasModel.glue {X U V W : Over (Sp K)} (u : U ⟶ X) (v : V ⟶ X) (p : W ⟶ U) (q : W ⟶ V)
    (hu : IsOpenImmersion u.left) (hv : IsOpenImmersion v.left) (h : IsPullback p.left q.left u.left v.left)
    (hc : ∀ x : X.left, x ∈ Set.range u.left ∨ x ∈ Set.range v.left)
    (h₁ : QuasiCompact W.hom) (h₂ : QuasiSeparated W.hom) (h₃ : LocallyOfFiniteType U.hom)
    (h₄ : LocallyOfFiniteType V.hom) (hU : HasModel U) (hV : HasModel V) (hW : HasModel W) : HasModel X := by sorry
