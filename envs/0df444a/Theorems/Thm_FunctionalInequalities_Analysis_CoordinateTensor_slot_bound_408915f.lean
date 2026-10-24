-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_bound_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.slot_bound_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:46.563104+00:00
-- url     : https://prove2.me/theorems/02635a2a-b76c-412c-9ec2-f8759c9f7fc6
-- title:
--   Tensor Slot Bound From a Matrix Family Bound
-- statement:
--   This private auxiliary lemma lifts a vector inequality to one tensor slot.
--
--   Let $H_i$ be a family of real $n\times n$ matrices satisfying, for every vector $v\in\mathbb R^n$,
--
--   $$
--   \sum_i\|H_i v\|^2\le 8\|v\|^2.
--   $$
--
--   Then for every order-$r$ coordinate tensor $T$ and every slot $s$,
--
--   $$
--   \sum_i\|H_i^{(s)}T\|^2\le 8\|T\|^2.
--   $$
--
--   This technical lifting result is used to control the slotwise terms in the drift estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L45-L134 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `_private.FunctionalInequalities.Analysis.Tensor.SlotAction.0.FunctionalInequalities.Analysis.CoordinateTensor.slot_bound`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.CoordinateTensor
end FunctionalInequalities.Analysis.CoordinateTensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.CoordinateTensor
variable {n r : ℕ}

lemma FunctionalInequalities.Analysis.CoordinateTensor.slot_bound_408915f (H : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (h8 : ∀ v : Fin n → ℝ, ∑ i, ∑ a, (∑ b, H i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2)
    (T : (Fin r → Fin n) → ℝ) (s : Fin r) :
    ∑ i, ∑ J, (∑ k, H i (J s) k * T (Function.update J s k)) ^ 2 ≤
      8 * ∑ J, T J ^ 2 := by sorry
