-- Prove2me | Theorems.Thm_GlobalTheory_fixed_mem_of_orbit_height
-- name    : GlobalTheory.fixed_mem_of_orbit_height
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:50:45.544296+00:00
-- url     : https://prove2.me/theorems/1db1978b-d807-412a-9b14-66ae8a94629a
-- title:
--   Global Theory: fixed mem of orbit height
-- statement:
--   The Global Theory construction uses the fixed mem of orbit height property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L205-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L205-L258

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_FixedMemOfOrbitHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule MulAction
open GlobalTheory
open GlobalTheory.GradedFixed

theorem GlobalTheory.fixed_mem_of_orbit_height : ∀ {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (V : ι → Submodule ℂ M), iSupIndep V → (⨆ i, V i) = ⊤ →
    (∀ i, ∃ v : M, V i ≤ Submodule.span ℂ {v}) → (∀ (g : G) (i : ι), (V i).map (π g) ≤ V (g • i)) →
    ∀ (μ : ι → ℕ), (∀ (g : G) (i : ι), μ (g • i) = μ i) → ∀ (S : Submodule ℂ M), (∀ v ∈ S, ∀ g, π g v = v) →
    (∀ i, (∃ w : M, w ≠ 0 ∧ (∀ g, π g w = w) ∧ w ∈ ⨆ g : G, V (g • i)) →
      ∃ v ∈ S, ∃ u ∈ ⨆ (j) (_ : μ j < μ i), V j, v - u ∈ (⨆ g : G, V (g • i)) ∧ v - u ≠ 0) →
    ∀ w : M, (∀ g, π g w = w) → w ∈ S := by sorry
