-- Prove2me | Theorems.Thm_GlobalTheory_FinAffineCharts_exists_finite_affine_cover
-- name    : GlobalTheory.FinAffineCharts.exists_finite_affine_cover
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:14.460563+00:00
-- url     : https://prove2.me/theorems/c1f3d389-5b5c-4750-8bee-71f7696273ed
-- title:
--   Fin Affine Charts: exists finite affine cover
-- statement:
--   The Fin Affine Charts construction uses the exists finite affine cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteAffineCharts.lean#L67-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteAffineCharts.lean#L67-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteAffineCharts
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.FinAffineCharts
variable {X : Scheme.{0}}

theorem GlobalTheory.FinAffineCharts.exists_finite_affine_cover [CompactSpace X] (M : LB X) (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → X.Opens) (c : κ → M.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (c a)) ∧ ⨆ a, W a = ⊤ := by sorry
