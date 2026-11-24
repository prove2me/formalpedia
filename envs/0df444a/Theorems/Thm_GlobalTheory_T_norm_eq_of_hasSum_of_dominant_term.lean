-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_eq_of_hasSum_of_dominant_term
-- name    : GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:35.408745+00:00
-- url     : https://prove2.me/theorems/4e4051a4-0c81-42df-a3a1-a37030a74609
-- title:
--   T: norm eq of has Sum of dominant term
-- statement:
--   The T construction uses the norm eq of has Sum of dominant term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormHasSumEqOfDominantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormHasSumEqOfDominantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormHasSumEqOfDominant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormHasSumEqOfDominantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by sorry
