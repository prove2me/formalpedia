-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_slot_sum_two_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:49.710427+00:00
-- url     : https://prove2.me/theorems/419bf605-df3b-4d83-bd65-89b740a8ab14
-- title:
--   One-Slot Delta Collapse With Two Tensors
-- statement:
--   This private auxiliary lemma evaluates a two-tensor coordinate sum with delta constraints.
--
--   For coordinate tensors $S,T$, a real matrix $M$, and order $r$ and dimension $n$, the sum
--
--   $$
--   \sum_{J,K}S_JT_K\sum_s
--   \left(\prod_{u\ne s}\delta_{J_u,K_u}\right)(-M_{J_sK_s})
--   $$
--
--   is equal to
--
--   $$
--   -\langle S,\Sigma_M T\rangle.
--   $$
--
--   Here $\Sigma_M T=\sum_sM^{(s)}T$. The lemma is an internal algebraic component of the energy-form derivative calculation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L678-L736 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
open Matrix
open scoped RealInnerProductSpace
section S3Bf3B2SecondOrderCore
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

lemma FunctionalInequalities.Analysis.CoordinateTensor.slot_sum_two_408915f
    (S T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      S J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -inner S (actSum M T) := by sorry
