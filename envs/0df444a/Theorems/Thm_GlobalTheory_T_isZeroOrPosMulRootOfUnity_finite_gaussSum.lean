-- Prove2me | Theorems.Thm_GlobalTheory_T_isZeroOrPosMulRootOfUnity_finite_gaussSum
-- name    : GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:02.842913+00:00
-- url     : https://prove2.me/theorems/27ad8ddb-6c27-4c0a-ab5d-16fb9497db53
-- title:
--   T: is Zero Or Pos Mul Root Of Unity finite gauss Sum
-- statement:
--   The T construction uses the is Zero Or Pos Mul Root Of Unity finite gauss Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by sorry
