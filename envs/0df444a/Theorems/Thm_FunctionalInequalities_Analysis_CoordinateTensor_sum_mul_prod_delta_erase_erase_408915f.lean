-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_sum_mul_prod_delta_erase_erase_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:07.239403+00:00
-- url     : https://prove2.me/theorems/10dc13a5-e19b-4e6a-9698-a0dd6f1292c0
-- title:
--   Two-Slot Delta Collapse
-- statement:
--   This statement evaluates delta constraints leaving two tensor slots free.
--
--   Let $J:\operatorname{Fin}(r)\to\operatorname{Fin}(n)$, let distinct slots $s,t\in\operatorname{Fin}(r)$ satisfy $s\ne t$, and let $f$ be real-valued on coordinate tensors. Then
--
--   $$
--   \sum_{J'}f(J')\prod_{u\notin\{s,t\}}\delta_{J_u,J'_u}
--   =\sum_{k,l\in\operatorname{Fin}(n)}f(J[s\mapsto k][t\mapsto l]).
--   $$
--
--   The identity is a finite reindexing tool for sums with all coordinates fixed except two.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L494-L586 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf3B1SecondOrderHelpers
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

theorem FunctionalInequalities.Analysis.CoordinateTensor.sum_mul_prod_delta_erase_erase_408915f (J : Fin r → Fin n) {s t : Fin r} (hst : s ≠ t)
    (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' *
        ∏ s' ∈ (Finset.univ.erase s).erase t, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by sorry
