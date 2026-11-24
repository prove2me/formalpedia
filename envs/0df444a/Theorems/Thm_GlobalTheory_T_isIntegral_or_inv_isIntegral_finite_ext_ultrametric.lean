-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_or_inv_isIntegral_finite_ext_ultrametric
-- name    : GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:18.379801+00:00
-- url     : https://prove2.me/theorems/38a405af-f5ac-4e49-bdfc-a69722990a06
-- title:
--   T: is Integral or inv is Integral finite ext ultrametric
-- statement:
--   The T construction uses the is Integral or inv is Integral finite ext ultrametric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by sorry
