-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_chart_data
-- name    : GlobalTheory.FiniteCover.chart_data
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:17.713415+00:00
-- url     : https://prove2.me/theorems/919c7940-6eab-431c-91b7-6932dfefa14d
-- title:
--   Finite Cover: chart data
-- statement:
--   The Finite Cover construction uses the chart data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinrankSecPullSandwich.lean#L35-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FinrankSecPullSandwich.lean#L35-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCommonMultiple
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FinrankSecPullSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']

theorem GlobalTheory.FiniteCover.chart_data (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ]
    [Algebra X.functionField X'.functionField]
    (hF : ∀ x, algebraMap X.functionField X'.functionField x = functionFieldMap φ x)
    {D : X.Opens} (hD : IsAffineOpen D) (h : genericPoint X ∈ D) :
    (∃ x, Module.finrank X.functionField X'.functionField = φ.finrank x) ∧
    ∀ {d : ℕ} (e : Module.Basis (Fin d) X.functionField X'.functionField),
      ∃ c ∈ (toField h).range, c ≠ 0 ∧
        (∀ j, ∀ y ∈ (toField (generic_mem_preimage φ h)).range, c * e.repr y j ∈ (toField h).range) ∧
        ∀ j, c • e j ∈ (toField (generic_mem_preimage φ h)).range := by sorry
