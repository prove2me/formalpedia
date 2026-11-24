-- Prove2me | Theorems.Thm_GlobalTheory_GeneratorFunctor_isRepresentable_of_charts
-- name    : GlobalTheory.GeneratorFunctor.isRepresentable_of_charts
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:59.218262+00:00
-- url     : https://prove2.me/theorems/8861f7be-5ddb-4a76-8970-42bb36528254
-- title:
--   Generator Functor: is Representable of charts
-- statement:
--   The Generator Functor construction uses the is Representable of charts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L21-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L21-L71

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

theorem GlobalTheory.GeneratorFunctor.isRepresentable_of_charts (F : Scheme.{0}ᵒᵖ ⥤ Type)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) {J : Type} (X : J → Scheme.{0})
    (x : ∀ j, F.obj (op (X j))) (W : ∀ (_ : J) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens)
    (hW : ∀ j (Z : Scheme.{0}) (y : F.obj (op Z)) (Z' : Scheme.{0}) (a : Z' ⟶ Z),
      Set.range a ⊆ (W j Z y : Set Z) ↔ ∃ g : Z' ⟶ X j, F.map g.op (x j) = F.map a.op y)
    (inj : ∀ j (Z : Scheme.{0}) (g g' : Z ⟶ X j), F.map g.op (x j) = F.map g'.op (x j) → g = g')
    (cov : ∀ (Z : Scheme.{0}) (y : F.obj (op Z)) (z : Z), ∃ j, z ∈ W j Z y) :
    F.IsRepresentable := by sorry
