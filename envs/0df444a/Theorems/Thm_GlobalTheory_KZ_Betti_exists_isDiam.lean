-- Prove2me | Theorems.Thm_GlobalTheory_KZ_Betti_exists_isDiam
-- name    : GlobalTheory.KZ.Betti.exists_isDiam
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:46:42.156804+00:00
-- url     : https://prove2.me/theorems/8d498d2f-6717-4aaa-a043-2d97f49b49e8
-- title:
--   Betti: exists is Diam
-- statement:
--   The Betti construction uses the exists is Diam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L88-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L88-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti

theorem GlobalTheory.KZ.Betti.exists_isDiam {N l d : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (hd : Nat.Coprime d N) : ∃ γ, IsDiam N l d γ := by sorry
