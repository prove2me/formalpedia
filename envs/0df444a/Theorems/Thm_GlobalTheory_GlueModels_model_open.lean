-- Prove2me | Theorems.Thm_GlobalTheory_GlueModels_model_open
-- name    : GlobalTheory.GlueModels.model_open
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:55:32.18805+00:00
-- url     : https://prove2.me/theorems/32aa8b21-dfeb-4239-843a-149e55cd205d
-- title:
--   Glue Models: model open
-- statement:
--   The Glue Models construction uses the model open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L86-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GlueModels
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.GlueModels.model_open {k K : Type} [Field k] [Field K] (β : k →+* K) {U W : Over (Sp K)} (p : W ⟶ U)
    [IsOpenImmersion p.left] {U₀ W₀ : Over (Sp k)} {φU : U.left ⟶ U₀.left} {φW : W.left ⟶ W₀.left}
    (hU : IsPullback φU U.hom U₀.hom (spMap β)) (hW : IsPullback φW W.hom W₀.hom (spMap β))
    (p₀ : W₀ ⟶ U₀) (hp : φW ≫ p₀.left = p.left ≫ φU) :
    IsPullback φW p.left p₀.left φU ∧ IsOpenImmersion p₀.left := by sorry
