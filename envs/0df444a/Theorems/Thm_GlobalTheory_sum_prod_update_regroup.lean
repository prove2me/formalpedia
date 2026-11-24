-- Prove2me | Theorems.Thm_GlobalTheory_sum_prod_update_regroup
-- name    : GlobalTheory.sum_prod_update_regroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:56.632317+00:00
-- url     : https://prove2.me/theorems/9222472a-6d9f-4af6-a514-d9658df92936
-- title:
--   Global Theory: sum prod update regroup
-- statement:
--   The Global Theory construction uses the sum prod update regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SumProdUpdateRegroup.lean#L19-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SumProdUpdateRegroup.lean#L19-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SumProdUpdateRegroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory

theorem GlobalTheory.sum_prod_update_regroup : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} {W : ι → Type}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    {m : ι → ℕ} (k : ∀ i, Fin (m i) → X i) (ℓ : ∀ i, Fin (m i) → W i →ₗ[ℂ] ℂ) (i₀ : ι)
    (F F' : (∀ i, X i) → ℂ) (w w' : W i₀)
    (hone : ∀ J : (∀ i, Fin (m i)), ∑ j, ℓ i₀ j w' * F (Function.update (fun i => k i (J i)) i₀ (k i₀ j)) =
      ∑ j, ℓ i₀ j w * F' (Function.update (fun i => k i (J i)) i₀ (k i₀ j)))
    (v : ∀ i, W i), ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w' i)) * F (fun i => k i (J i)) =
    ∑ J : (∀ i, Fin (m i)), (∏ i, ℓ i (J i) (Function.update v i₀ w i)) * F' (fun i => k i (J i)) := by sorry
