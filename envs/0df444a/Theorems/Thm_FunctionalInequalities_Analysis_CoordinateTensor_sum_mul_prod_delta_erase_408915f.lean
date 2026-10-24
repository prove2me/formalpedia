-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:08.218132+00:00
-- url     : https://prove2.me/theorems/48ca44ea-2ca1-4c6e-9620-dae04c6b58c0
-- title:
--   One-Slot Delta Collapse
-- statement:
--   This statement evaluates a finite sum constrained by Kronecker-delta factors.
--
--   Let $J:\operatorname{Fin}(r)\to\operatorname{Fin}(n)$, let $s\in\operatorname{Fin}(r)$, and let $f$ be a real-valued function on coordinate tensors. Then
--
--   $$
--   \sum_{J'}f(J')\prod_{s'\ne s}\delta_{J_{s'},J'_{s'}}
--   =\sum_{k\in\operatorname{Fin}(n)}f(J[s\mapsto k]).
--   $$
--
--   The product forces $J'$ to agree with $J$ outside slot $s$, leaving only the value in slot $s$ free. This finite combinatorial identity is used to collapse coordinate sums.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L94-L154 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf2EnergyFormFirstOrder
open Matrix
open scoped RealInnerProductSpace
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

theorem FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_408915f (J : Fin r → Fin n) (s : Fin r) (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, f (Function.update J s k) := by sorry
