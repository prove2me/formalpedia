-- Prove2me | Theorems.Thm_GlobalTheory_polarisation_on_subspace
-- name    : GlobalTheory.polarisation_on_subspace
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:44.561702+00:00
-- url     : https://prove2.me/theorems/a2b503e9-fa4b-4229-84e8-964ae11c00a2
-- title:
--   Global Theory: polarisation on subspace
-- statement:
--   The Global Theory construction uses the polarisation on subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PolarisationOnSubspace.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PolarisationOnSubspace.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PolarisationOnSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.polarisation_on_subspace : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : V → Prop) (B T : V → V → ℂ), (∀ (a : ℂ) x y, S x → S y → S (x + a • y)) → (∀ (a : ℂ) x y, S x → S y → B (x + a • y) (x + a • y) = B x x + a * B y x + (starRingEnd ℂ) a * B x y + a * (starRingEnd ℂ) a * B y y) → (∀ (a : ℂ) x y, S x → S y → T (x + a • y) (x + a • y) = T x x + a * T y x + (starRingEnd ℂ) a * T x y + a * (starRingEnd ℂ) a * T y y) → (∀ x, S x → B x x = T x x) → ∀ x y, S x → S y → B x y = T x y := by sorry
