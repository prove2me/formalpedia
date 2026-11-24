-- Prove2me | Theorems.Thm_GlobalTheory_KS_DerMor_appLE_app_of_section
-- name    : GlobalTheory.KS.DerMor.appLE_app_of_section
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:43:25.3198+00:00
-- url     : https://prove2.me/theorems/a1cd5410-f357-40c7-9634-2376b0fb5887
-- title:
--   Der Mor: app LE app of section
-- statement:
--   The Der Mor construction uses the app LE app of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomFromConstThickeningOfDerivation.lean#L92-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHomFromConstThickeningOfDerivation.lean#L92-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMor

theorem GlobalTheory.KS.DerMor.appLE_app_of_section {Y Y' : Scheme.{0}} (ρ : Y' ⟶ Y) (j : Y ⟶ Y') (h : j ≫ ρ = 𝟙 Y)
    (O : Y.Opens) (e : O ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ O)) (a : Γ(Y, O)) :
    (j.appLE (ρ ⁻¹ᵁ O) O e).hom ((ρ.app O).hom a) = a := by sorry
