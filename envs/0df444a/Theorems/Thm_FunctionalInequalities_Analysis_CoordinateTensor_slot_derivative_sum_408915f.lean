-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_derivative_sum_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:16.336047+00:00
-- url     : https://prove2.me/theorems/9bcc902d-3bcf-46b6-8f90-da09cd95503e
-- title:
--   Derivative Sum for One-Slot Energy Terms
-- statement:
--   This private auxiliary lemma evaluates the first-order matrix contribution in a coordinate-tensor energy calculation.
--
--   For an order-$r$ coordinate tensor $T$ and a real matrix $M$, the finite sum
--
--   $$
--   \sum_{J,K}T_JT_K\sum_s
--   \left(\prod_{u\ne s}\delta_{J_u,K_u}\right)(-M_{J_sK_s})
--   $$
--
--   equals
--
--   $$
--   -\langle T,\Sigma_M T\rangle.
--   $$
--
--   The result is a purely finite algebraic identity used internally in differentiating the energy form.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L233-L291 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum`; the repository is private at upload time).

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

lemma FunctionalInequalities.Analysis.CoordinateTensor.slot_derivative_sum_408915f
    (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      T J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -inner T (actSum M T) := by sorry
