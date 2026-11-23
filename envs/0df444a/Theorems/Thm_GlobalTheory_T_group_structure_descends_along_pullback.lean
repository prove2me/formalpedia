-- Prove2me | Theorems.Thm_GlobalTheory_T_group_structure_descends_along_pullback
-- name    : GlobalTheory.T.group_structure_descends_along_pullback
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:39.914235+00:00
-- url     : https://prove2.me/theorems/59d263d1-fc14-439f-99d6-f15003fa64d6
-- title:
--   T: group structure descends along pullback
-- statement:
--   The T construction uses the group structure descends along pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescendsStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescendsStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescendsStatement
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

theorem GlobalTheory.T.group_structure_descends_along_pullback : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by sorry
