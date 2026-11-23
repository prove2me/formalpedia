-- Prove2me | Theorems.Thm_GlobalTheory_SS_GlueCompat_closed_two
-- name    : GlobalTheory.SS.GlueCompat.closed_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:59:14.254948+00:00
-- url     : https://prove2.me/theorems/a91bdbd2-18db-4310-ae8e-3b5fc4434fc1
-- title:
--   Glue Compat: closed two
-- statement:
--   The Glue Compat construction uses the closed two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L73-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGlueFinitelyManyCompatibleSmoothModels.lean#L73-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
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
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.SS.GlueCompat.closed_two {S : Scheme.{0}} {X N G M₁ M₂ W₁ W₂ : Over S} (p : X ⟶ N) (q : X ⟶ G) {g₁ : M₁ ⟶ G} {g₂ : M₂ ⟶ G}
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    (hc : ∀ x : G.left, x ∈ Set.range g₁.left ∨ x ∈ Set.range g₂.left)
    {a₁ : W₁ ⟶ X} {b₁ : W₁ ⟶ M₁} {a₂ : W₂ ⟶ X} {b₂ : W₂ ⟶ M₂}
    (h₁ : IsPullback a₁.left b₁.left q.left g₁.left) (h₂ : IsPullback a₂.left b₂.left q.left g₂.left)
    (c₁ : IsClosedImmersion (lift (a₁ ≫ p) b₁).left) (c₂ : IsClosedImmersion (lift (a₂ ≫ p) b₂).left) :
    IsClosedImmersion (lift p q).left := by sorry
