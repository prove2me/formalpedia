-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_inner_actSum_actSum_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:50.307581+00:00
-- url     : https://prove2.me/theorems/022548f3-d5a1-4b55-8af7-ec7c0c5fc239
-- title:
--   Expansion of the Squared Slot-Sum Action
-- statement:
--   This statement expands the inner product of a coordinate tensor with its summed slot action.
--
--   Let $M$ be a symmetric real $n\times n$ matrix and let $T:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$. Then
--
--   $$
--   \begin{aligned}
--   \langle \Sigma_M T,\Sigma_M T\rangle
--   &=\sum_s\langle M^{(s)}T,M^{(s)}T\rangle\\
--   &\quad+\sum_s\sum_{t\in\operatorname{Fin}(r)\setminus\{s\}}
--   \langle T,M^{(s)}(M^{(t)}T)\rangle,
--   \end{aligned}
--   $$
--
--   where $\Sigma_M T=\sum_s M^{(s)}T$, implemented by `actSum`. This is the diagonal/off-diagonal decomposition used in the coordinate-tensor drift algebra.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean#L411-L459 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.SlotAction`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.CoordinateTensor.inner_actSum_actSum_408915f (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (T : (Fin r → Fin n) → ℝ) :
    inner (actSum M T) (actSum M T) =
      ∑ s, inner (actOn M s T) (actOn M s T) +
        ∑ s, ∑ t ∈ Finset.univ.erase s, inner T (actOn M s (actOn M t T)) := by sorry
