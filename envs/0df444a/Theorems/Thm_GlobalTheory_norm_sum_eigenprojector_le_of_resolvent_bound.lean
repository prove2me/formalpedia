-- Prove2me | Theorems.Thm_GlobalTheory_norm_sum_eigenprojector_le_of_resolvent_bound
-- name    : GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:25.017466+00:00
-- url     : https://prove2.me/theorems/de6b1403-2a96-425a-8282-821df291f75e
-- title:
--   Global Theory: norm sum eigenprojector le of resolvent bound
-- statement:
--   The Global Theory construction uses the norm sum eigenprojector le of resolvent bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NormSumEigenprojectorLeOfResolventBound.lean#L28-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NormSumEigenprojectorLeOfResolventBound.lean#L28-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NormSumEigenprojectorLeOfResolventBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
open GlobalTheory
open Finset Complex
open scoped InnerProductSpace

theorem GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ]
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (In : Finset κ)
    (c : ℂ) (R Mc : ℝ), FiniteDimensional ℂ VV → 0 < R → 0 ≤ Mc →
    (∀ x ∈ VV, ∑ i, p i x = x) →
    (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) →
    (∀ i ∈ In, ‖lam i - c‖ < R) → (∀ i, i ∉ In → R < ‖lam i - c‖) →
    (∀ ζ : ℂ, ‖ζ - c‖ = R → ∀ x ∈ VV, ‖x‖ ≤ Mc * ‖ζ • x - T x‖) →
    ∀ x ∈ VV, ‖∑ i ∈ In, p i x‖ ≤ R * Mc * ‖x‖ := by sorry
