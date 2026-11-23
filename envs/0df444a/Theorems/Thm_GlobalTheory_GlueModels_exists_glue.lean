-- Prove2me | Theorems.Thm_GlobalTheory_GlueModels_exists_glue
-- name    : GlobalTheory.GlueModels.exists_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:17.566775+00:00
-- url     : https://prove2.me/theorems/5e7c68d2-9fff-41fe-86b0-62a0e4915ce9
-- title:
--   Glue Models: exists glue
-- statement:
--   The Glue Models construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GlueModelsOverSubfield.lean#L14-L35

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

theorem GlobalTheory.GlueModels.exists_glue {X U V W Y : Scheme.{0}} {u : U ⟶ X} {v : V ⟶ X} {p : W ⟶ U} {q : W ⟶ V}
    [IsOpenImmersion u] [IsOpenImmersion v] (h : IsPullback p q u v)
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (a : U ⟶ Y) (b : V ⟶ Y) (hab : p ≫ a = q ≫ b) :
    ∃ φ : X ⟶ Y, u ≫ φ = a ∧ v ≫ φ = b := by sorry
