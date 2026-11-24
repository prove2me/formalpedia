-- Prove2me | Theorems.Thm_GlobalTheory_GeneratorFunctor_Pt_ext_chart
-- name    : GlobalTheory.GeneratorFunctor.Pt.ext_chart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:54:25.465806+00:00
-- url     : https://prove2.me/theorems/aa48cc02-6bfa-4039-b001-53ffb9603745
-- title:
--   Pt: ext chart
-- statement:
--   The Pt construction uses the ext chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L351-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/InverseBundleGeneratorPointOfChartUnitsSections.lean#L351-L359

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
variable {B : Scheme.{0}} {κ : Type} (N : κ → LB B)
variable {N}

theorem GlobalTheory.GeneratorFunctor.Pt.ext_chart {Z : Scheme.{0}} {x y : Pt N Z} (hb : x.b = y.b) (j : ∀ k, (N k).ι)
    (hx : ∀ k, ⊤ ≤ 𝟙 Z ⁻¹ᵁ x.b ⁻¹ᵁ (N k).U (j k)) (hy : ∀ k, ⊤ ≤ 𝟙 Z ⁻¹ᵁ y.b ⁻¹ᵁ (N k).U (j k))
    (hs : ∀ k, pb (𝟙 Z) _ ⊤ (hx k) (x.s k (j k)) = pb (𝟙 Z) _ ⊤ (hy k) (y.s k (j k))) :
    x = y := by sorry
