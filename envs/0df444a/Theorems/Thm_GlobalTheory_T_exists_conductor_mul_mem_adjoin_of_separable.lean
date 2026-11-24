-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_conductor_mul_mem_adjoin_of_separable
-- name    : GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:34:46.480235+00:00
-- url     : https://prove2.me/theorems/749818a6-36ce-4fea-94a7-b0f112b80acb
-- title:
--   T: exists conductor mul mem adjoin of separable
-- statement:
--   The T construction uses the exists conductor mul mem adjoin of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsConductorMulMemAdjoinOfSeparableStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsConductorMulMemAdjoinOfSeparableStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparable
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsConductorMulMemAdjoinOfSeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g → ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u → algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by sorry
