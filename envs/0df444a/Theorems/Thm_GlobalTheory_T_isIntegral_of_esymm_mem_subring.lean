-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_of_esymm_mem_subring
-- name    : GlobalTheory.T.isIntegral_of_esymm_mem_subring
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:37.90081+00:00
-- url     : https://prove2.me/theorems/5bcba13f-77d7-4b93-bbf6-e17f295f7059
-- title:
--   T: is Integral of esymm mem subring
-- statement:
--   The T construction uses the is Integral of esymm mem subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfEsymmMemSubringStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfEsymmMemSubringStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubring
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfEsymmMemSubringStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_of_esymm_mem_subring : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by sorry
