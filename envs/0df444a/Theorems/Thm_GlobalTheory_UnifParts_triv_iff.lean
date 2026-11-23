-- Prove2me | Theorems.Thm_GlobalTheory_UnifParts_triv_iff
-- name    : GlobalTheory.UnifParts.triv_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:52.912137+00:00
-- url     : https://prove2.me/theorems/16208ba7-cdb3-4d74-945f-e5d87c81accc
-- title:
--   Unif Parts: triv iff
-- statement:
--   The Unif Parts construction uses the triv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FamilyUnifOfParts.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FamilyUnifOfParts.lean#L87-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FamilyUnifOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.UnifParts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.UnifParts.triv_iff {D D' : Datum H} (l : Level H) (t : D.La →ₗ[𝓞 E] D'.La)
    (ht : ∀ b, ∃ a e, b = t a + l.M' • e) (gam : D'.La ≃ₗ[𝓞 E] D'.La) (I : Ideal (𝓞 E)) (n : ℕ) (hn : n ∣ l.M') :
    (∀ a ∈ I • (⊤ : Submodule (𝓞 E) D.La), ∃ x, gam (t a) = t a + n • x) ↔
      ∀ a ∈ I • (⊤ : Submodule (𝓞 E) D'.La), ∃ x, gam a = a + n • x := by sorry
