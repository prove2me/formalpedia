-- Prove2me | Theorems.Thm_GlobalTheory_eventually_eq_zero_of_slices
-- name    : GlobalTheory.eventually_eq_zero_of_slices
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:16.389706+00:00
-- url     : https://prove2.me/theorems/74fb2bdd-1b99-45e3-bf08-3ca17557d5a5
-- title:
--   Global Theory: eventually eq zero of slices
-- statement:
--   The Global Theory construction uses the eventually eq zero of slices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAnalyticParamInverse.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAnalyticParamInverse.lean#L60-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticParamInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Metric Set Filter Asymptotics
open scoped Topology
variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
omit [FiniteDimensional ℂ B] [FiniteDimensional ℂ V]

theorem GlobalTheory.eventually_eq_zero_of_slices {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [CompleteSpace V] {F : B × W → V} {b₀ : B} (hF : AnalyticAt ℂ F (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, ∀ᶠ w in 𝓝 (0 : W), F (b, w) = 0) :
    ∀ᶠ q in 𝓝 ((b₀, 0) : B × W), F q = 0 := by sorry
