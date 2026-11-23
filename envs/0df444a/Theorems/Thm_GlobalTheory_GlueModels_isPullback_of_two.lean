-- Prove2me | Theorems.Thm_GlobalTheory_GlueModels_isPullback_of_two
-- name    : GlobalTheory.GlueModels.isPullback_of_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:34.313524+00:00
-- url     : https://prove2.me/theorems/66ec234e-843a-4c74-be02-b7fc1b1c6b62
-- title:
--   Glue Models: is Pullback of two
-- statement:
--   The Glue Models construction uses the is Pullback of two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L37-L56

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

theorem GlobalTheory.GlueModels.isPullback_of_two {W X Y Z U V U' V' : Scheme.{0}} {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {u : U ⟶ X} {v : V ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    {u' : U' ⟶ W} {v' : V' ⟶ W} {aU : U' ⟶ U} {aV : V' ⟶ V}
    (hU : IsPullback aU u' u a) (hV : IsPullback aV v' v a)
    (hU' : IsPullback aU (u' ≫ b) (u ≫ f) g) (hV' : IsPullback aV (v' ≫ b) (v ≫ f) g) :
    IsPullback a b f g := by sorry
