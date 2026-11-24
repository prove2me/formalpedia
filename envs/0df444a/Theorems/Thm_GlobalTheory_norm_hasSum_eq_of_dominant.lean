-- Prove2me | Theorems.Thm_GlobalTheory_norm_hasSum_eq_of_dominant
-- name    : GlobalTheory.norm_hasSum_eq_of_dominant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:23.1122+00:00
-- url     : https://prove2.me/theorems/6ef876eb-8510-4949-aaaf-aed383232eff
-- title:
--   Global Theory: norm has Sum eq of dominant
-- statement:
--   The Global Theory construction uses the norm has Sum eq of dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormHasSumEqOfDominant.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormHasSumEqOfDominant.lean#L6-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormHasSumEqOfDominant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.norm_hasSum_eq_of_dominant : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type)
    (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by sorry
