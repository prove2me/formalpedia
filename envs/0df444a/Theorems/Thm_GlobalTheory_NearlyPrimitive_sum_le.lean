-- Prove2me | Theorems.Thm_GlobalTheory_NearlyPrimitive_sum_le
-- name    : GlobalTheory.NearlyPrimitive.sum_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:43.198406+00:00
-- url     : https://prove2.me/theorems/41b00b9e-d6c1-4d35-8cc7-e42a422e2f65
-- title:
--   Nearly Primitive: sum le
-- statement:
--   The Nearly Primitive construction uses the sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean#L92-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NearlyPrimitive
open Finset Filter Topology

theorem GlobalTheory.NearlyPrimitive.sum_le {B ι : Type} [AddCommGroup B] (N : B → ℝ) (h0 : N 0 = 0)
    (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y)) {T : ℝ} (hT : 0 ≤ T) (s : Finset ι) (f : ι → B)
    (hf : ∀ i ∈ s, N (f i) ≤ T) : N (∑ i ∈ s, f i) ≤ T := by sorry
