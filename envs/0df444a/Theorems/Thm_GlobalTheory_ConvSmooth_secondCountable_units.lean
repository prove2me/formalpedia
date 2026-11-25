-- Prove2me | Theorems.Thm_GlobalTheory_ConvSmooth_secondCountable_units
-- name    : GlobalTheory.ConvSmooth.secondCountable_units
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:31.730428+00:00
-- url     : https://prove2.me/theorems/e9df0ab2-4c12-4af2-9e1f-131532facaa0
-- title:
--   Conv Smooth: second Countable units
-- statement:
--   The Conv Smooth construction uses the second Countable units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L14-L17

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ConvSmooth

theorem GlobalTheory.ConvSmooth.secondCountable_units (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : SecondCountableTopology 𝔸ˣ := by sorry
