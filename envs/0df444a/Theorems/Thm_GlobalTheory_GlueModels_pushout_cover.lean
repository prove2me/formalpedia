-- Prove2me | Theorems.Thm_GlobalTheory_GlueModels_pushout_cover
-- name    : GlobalTheory.GlueModels.pushout_cover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:30.183462+00:00
-- url     : https://prove2.me/theorems/fa552616-6940-429a-8610-f14ef83e939a
-- title:
--   Glue Models: pushout cover
-- statement:
--   The Glue Models construction uses the pushout cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L66-L74

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

theorem GlobalTheory.GlueModels.pushout_cover {W U V : Scheme.{0}} (p : W ⟶ U) (q : W ⟶ V) [IsOpenImmersion p]
    [IsOpenImmersion q] (z : (pushout p q : Scheme.{0})) :
    z ∈ Set.range (pushout.inl p q) ∨ z ∈ Set.range (pushout.inr p q) := by sorry
