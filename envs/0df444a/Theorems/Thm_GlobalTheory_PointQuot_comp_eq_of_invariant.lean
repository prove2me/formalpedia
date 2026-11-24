-- Prove2me | Theorems.Thm_GlobalTheory_PointQuot_comp_eq_of_invariant
-- name    : GlobalTheory.PointQuot.comp_eq_of_invariant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:50.120507+00:00
-- url     : https://prove2.me/theorems/ba49ab20-2d79-40cf-8a26-783fea537bb0
-- title:
--   Point Quot: comp eq of invariant
-- statement:
--   The Point Quot construction uses the comp eq of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L195-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsQuotientByFiniteGroupOfPoints.lean#L195-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsQuotientByFiniteGroupOfPoints
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
open GlobalTheory
open GlobalTheory.PointQuot
variable {S : Scheme.{0}}

theorem GlobalTheory.PointQuot.comp_eq_of_invariant {I : Type} {A B Y : Over S} [GrpObj A] [GrpObj B]
    (x : I → (𝟙_ (Over S) ⟶ A)) (q : A ⟶ B) [IsMonHom q]
    (hker : IsPullback (constDesc x) (toUnit _) q η[B]) (f : A ⟶ Y)
    (hf : ∀ c, ((toUnit A ≫ x c) * 𝟙 A) ≫ f = f) {Z : Over S} (g g' : Z ⟶ A)
    (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by sorry
