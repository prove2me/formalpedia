-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actOn_left_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:50.193008+00:00
-- url     : https://prove2.me/theorems/1beded3a-e3a5-4156-a595-a95421de8a12
-- title:
--   Self-Adjointness of a Symmetric Slot Action
-- statement:
--   This statement proves self-adjointness of the action of a symmetric matrix on one tensor slot.
--
--   Let $M$ be a real $n\times n$ matrix satisfying $M^\mathsf T=M$. For $s\in\operatorname{Fin}(r)$ and coordinate tensors $T,S:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$, one has
--
--   $$
--   \langle M^{(s)}T,S\rangle
--   =\langle T,M^{(s)}S\rangle.
--   $$
--
--   Here the inner product is the finite coordinate-tensor inner product and $M^{(s)}$ is `actOn M s`. The identity is used to move symmetric slot actions between factors in tensor estimates.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L351-L403 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.CoordinateTensor.inner_actOn_left_408915f (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (s : Fin r)
    (T S : (Fin r → Fin n) → ℝ) : inner (actOn M s T) S = inner T (actOn M s S) := by sorry
