-- Prove2me | Theorems.Thm_GlobalTheory_ApproxOnto_eventually_onto
-- name    : GlobalTheory.ApproxOnto.eventually_onto
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:50.493273+00:00
-- url     : https://prove2.me/theorems/73631f4f-a178-5cf6-b0d8-c17fc26f902d
-- title:
--   Approx Onto: eventually onto
-- statement:
--   The Approx Onto construction uses the eventually onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EventuallyOnto.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/EventuallyOnto.lean#L8-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_EventuallyOnto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open Filter
open GlobalTheory GlobalTheory.ApproxOnto

theorem GlobalTheory.ApproxOnto.eventually_onto : ∀ (X : Type) (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] (T : ℕ → W →ₗ[ℂ] W), (∀ (ψ : W) (x : X), Tendsto (fun i => (T i ψ).1 x) atTop (𝓝 (ψ.1 x))) → ∃ i, Function.Surjective (T i) := by sorry
