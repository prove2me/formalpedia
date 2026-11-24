-- Prove2me | Theorems.Thm_GlobalTheory_JR_exists_selfDual_of_dual_subgroups
-- name    : GlobalTheory.JR.exists_selfDual_of_dual_subgroups
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:38:16.818408+00:00
-- url     : https://prove2.me/theorems/14f273a6-136b-48ea-93b1-ce5c064979e8
-- title:
--   JR: exists self Dual of dual subgroups
-- statement:
--   The JR construction uses the exists self Dual of dual subgroups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L296-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSelfDualOfDualSubgroups.lean#L296-L298

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

theorem GlobalTheory.JR.exists_selfDual_of_dual_subgroups : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → ℂ), Continuous (fun p : V × V => B p.1 p.2) → (∀ x y, B x y = B y x) → (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ y, B 0 y = 1) → (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)) → ∃ μ : MeasureTheory.Measure V, _root_.GlobalTheory.JR.SelfDual μ B := by sorry
