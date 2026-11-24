-- Prove2me | Theorems.Thm_GlobalTheory_GeneratorFunctor_exists_torus
-- name    : GlobalTheory.GeneratorFunctor.exists_torus
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:56:02.900427+00:00
-- url     : https://prove2.me/theorems/96533e30-7b18-412b-a4ec-c0c25c715be5
-- title:
--   Generator Functor: exists torus
-- statement:
--   The Generator Functor construction uses the exists torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L73-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L73-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InverseBundleGeneratorPointOfChartUnitsSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GeneratorFunctor
open Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.GeneratorFunctor.exists_torus (S : Scheme.{0}) (κ : Type) :
    ∃ (T : Scheme.{0}) (p : T ⟶ S) (t : κ → Γ(T, ⊤)ˣ),
      (∀ (Z : Scheme.{0}) (c : Z ⟶ S) (v : κ → Γ(Z, ⊤)ˣ), ∃ g : Z ⟶ T, g ≫ p = c ∧
        ∀ k, g.appTop.hom (t k).val = (v k).val) ∧
      ∀ (Z : Scheme.{0}) (g g' : Z ⟶ T), g ≫ p = g' ≫ p →
        (∀ k, g.appTop.hom (t k).val = g'.appTop.hom (t k).val) → g = g' := by sorry
