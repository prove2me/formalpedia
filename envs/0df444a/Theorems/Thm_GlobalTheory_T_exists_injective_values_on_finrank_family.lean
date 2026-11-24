-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_injective_values_on_finrank_family
-- name    : GlobalTheory.T.exists_injective_values_on_finrank_family
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:36:07.583719+00:00
-- url     : https://prove2.me/theorems/0904962e-2f3d-4574-b3f7-765d2db9dff5
-- title:
--   T: exists injective values on finrank family
-- statement:
--   The T construction uses the exists injective values on finrank family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankLeCardValuesStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankLeCardValuesStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_injective_values_on_finrank_family : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by sorry
