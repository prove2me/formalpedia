-- Prove2me | Theorems.Thm_GlobalTheory_analyticAt_param_doublingLog
-- name    : GlobalTheory.analyticAt_param_doublingLog
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:38:15.093458+00:00
-- url     : https://prove2.me/theorems/c11b17f8-53ce-47fd-aa3a-dca7092075fa
-- title:
--   Global Theory: analytic At param doubling Log
-- statement:
--   The Global Theory construction uses the analytic At param doubling Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAnalyticParamInverse.lean#L74-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAnalyticParamInverse.lean#L74-L145

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

theorem GlobalTheory.analyticAt_param_doublingLog {ε : B × V → V} {b₀ : B} (ha : AnalyticAt ℂ ε (b₀, 0))
    (h : ∀ᶠ b in 𝓝 b₀, (fun x => ε (b, x) - (2 : ℂ)⁻¹ • x) =O[𝓝 0] fun x => ‖x‖ ^ 2) :
    AnalyticAt ℂ (fun q : B × V => doublingLog (fun x => ε (q.1, x)) q.2) (b₀, 0) := by sorry
