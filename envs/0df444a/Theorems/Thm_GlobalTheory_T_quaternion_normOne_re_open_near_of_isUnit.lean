-- Prove2me | Theorems.Thm_GlobalTheory_T_quaternion_normOne_re_open_near_of_isUnit
-- name    : GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:56:55.415973+00:00
-- url     : https://prove2.me/theorems/d32b5fe5-d7fd-4043-9425-42b31b94474e
-- title:
--   T: quaternion norm One re open near of is Unit
-- statement:
--   The T construction uses the quaternion norm One re open near of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneReOpenNearOfIsUnitStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneReOpenNearOfIsUnitStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneReOpenNearOfIsUnit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneReOpenNearOfIsUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quaternion_normOne_re_open_near_of_isUnit : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (a b : R), SqOpen R → ∀ g : ℍ[R, a, b], nrm g = 1 → IsUnit (1 - g.re ^ 2) → ∀ W : Set ℍ[R, a, b], W ∈ 𝓝 g → ∃ O : Set R, IsOpen O ∧ g.re ∈ O ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by sorry
