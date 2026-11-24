-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChart_second_kind_chart
-- name    : GlobalTheory.UnitaryChart.second_kind_chart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:39:13.360323+00:00
-- url     : https://prove2.me/theorems/d6201272-42a6-4af9-87bd-11af280dc66b
-- title:
--   Unitary Chart: second kind chart
-- statement:
--   The Unitary Chart construction uses the second kind chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L110-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L110-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter

theorem GlobalTheory.UnitaryChart.second_kind_chart : ∀ (E : Type) [NormedRing E] [NormedAlgebra ℝ E] [FiniteDimensional ℝ E] (σ : E →ₗ[ℝ] E) (N : ℕ) (e : Fin N → E) (c : Fin N → ℝ → E), (∀ a, σ (σ a) = a) → (∀ a b, σ (a * b) = σ b * σ a) → σ 1 = 1 → LinearIndependent ℝ e → (∀ i, σ (e i) = -e i) → (∀ X, σ X = -X → X ∈ Submodule.span ℝ (Set.range e)) → (∀ i, c i 0 = 1 ∧ HasStrictDerivAt (c i) (e i) 0 ∧ ∀ t, σ (c i t) * c i t = 1 ∧ c i t * σ (c i t) = 1) → ∃ (s S K : ℝ) (W : Set E), 0 < s ∧ 0 ≤ K ∧ W ∈ nhds (1 : E) ∧ ∀ x ∈ W, σ x * x = 1 → x * σ x = 1 → ∃ f : (Fin N → ℝ) → (Fin N → ℝ), (∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖f t‖ ≤ S ∧ (List.ofFn fun i => c i (f t i)).prod * x = (List.ofFn fun i => c i (t i)).prod) ∧ ∀ t ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ∀ t' ∈ Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖t - t'‖ ≤ K * ‖f t - f t'‖ := by sorry
