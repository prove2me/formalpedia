-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_actOn_mul_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:49.571744+00:00
-- url     : https://prove2.me/theorems/b28ebd83-ae9f-44d1-aabc-cc541b680ead
-- title:
--   Composition of Matrix Actions on One Tensor Slot
-- statement:
--   This statement identifies the action of a matrix product on one slot of a coordinate tensor.
--
--   Let $n,r\in\mathbb N$, let $M,N$ be real $n\times n$ matrices, let $s\in\operatorname{Fin}(r)$, and let $T:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$. Then
--
--   $$
--   (MN)^{(s)}T=M^{(s)}\bigl(N^{(s)}T\bigr),
--   $$
--
--   where $A^{(s)}T$ denotes the Lean operation `actOn A s T`. This algebraic identity is used to manipulate slotwise matrix actions on coordinate tensors.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L314-L349 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
section S3Bf3ASlotActionAlgebra
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

theorem FunctionalInequalities.Analysis.CoordinateTensor.actOn_mul_408915f (M N : Matrix (Fin n) (Fin n) ℝ) (s : Fin r) (T : (Fin r → Fin n) → ℝ) :
    actOn (M * N) s T = actOn M s (actOn N s T) := by sorry
