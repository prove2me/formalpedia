-- Prove2me | Theorems.Thm_GlobalTheory_GradedFixed_exists_comp
-- name    : GlobalTheory.GradedFixed.exists_comp
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:39.153988+00:00
-- url     : https://prove2.me/theorems/b0f266ff-c28c-4cd4-bf47-eb15fe39ed3e
-- title:
--   Graded Fixed: exists comp
-- statement:
--   The Graded Fixed construction uses the exists comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L59-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/FixedMemOfOrbitHeight.lean#L59-L79

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
open GlobalTheory GlobalTheory.GradedFixed
variable {G ι M : Type} [Group G] [MulAction G ι] [AddCommGroup M] [Module ℂ M]

theorem GlobalTheory.GradedFixed.exists_comp (V : ι → Submodule ℂ M) (hV : iSupIndep V) (htop : (⨆ i, V i) = ⊤) :
    ∃ c : ι → M →ₗ[ℂ] M, (∀ i w, c i w ∈ V i) ∧ (∀ i v, v ∈ V i → c i v = v) ∧
      (∀ i j v, i ≠ j → v ∈ V j → c i v = 0) ∧ (∀ w, ∃ F : Finset ι, w = ∑ i ∈ F, c i w) := by sorry
