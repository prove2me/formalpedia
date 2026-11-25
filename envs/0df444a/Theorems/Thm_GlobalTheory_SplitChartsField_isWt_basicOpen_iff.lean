-- Prove2me | Theorems.Thm_GlobalTheory_SplitChartsField_isWt_basicOpen_iff
-- name    : GlobalTheory.SplitChartsField.isWt_basicOpen_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:05.207189+00:00
-- url     : https://prove2.me/theorems/81b10b16-f2d6-517d-ae5a-71a7dcee3539
-- title:
--   Split Charts Field: is Wt basic Open iff
-- statement:
--   The Split Charts Field construction uses the is Wt basic Open iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitChartsTorusExtensionOverField.lean#L62-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitChartsTorusExtensionOverField.lean#L62-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeightZeroSumOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitChartsTorusExtensionOverField
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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.SplitChartsField
open GlobalTheory.UU GlobalTheory.AffineThickening GlobalTheory.TorusQuotientLift GlobalTheory.LocalWeightUnits
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {B : Scheme.{0}}
  {i : splitTorus S X ⟶ G} {q : G.left ⟶ B} [IsAffineHom q] {V : B.Opens} (hi : IsMonHom i) (hV : IsAffineOpen V)
  (h₀ : ∀ a : Γ(G.left, q ⁻¹ᵁ V), IsWt i _ a 0 ↔ ∃ c, (q.app V).hom c = a)
  (hinj : Function.Injective (q.app V).hom) (hS : Stable i (q ⁻¹ᵁ V))
include hi hV h₀ hS

theorem GlobalTheory.SplitChartsField.isWt_basicOpen_iff (c : Γ(B, V)) (a : Γ(G.left, q ⁻¹ᵁ B.basicOpen c)) :
    IsWt i _ a 0 ↔ ∃ c', (q.app (B.basicOpen c)).hom c' = a := by sorry
