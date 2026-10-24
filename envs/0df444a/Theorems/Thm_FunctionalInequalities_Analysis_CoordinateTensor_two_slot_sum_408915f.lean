-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_two_slot_sum_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:06.520496+00:00
-- url     : https://prove2.me/theorems/427be618-ec66-44a3-abad-1c755915801b
-- title:
--   Two-Slot Mixed Delta Collapse
-- statement:
--   This private auxiliary lemma evaluates the mixed two-slot term arising from two matrix factors.
--
--   For a coordinate tensor $T$ and a real matrix $M$, the sum with two distinct slots and delta constraints equals
--
--   $$
--   \sum_s\sum_{u\ne s}
--   \left\langle T,M^{(s)}(M^{(u)}T)\right\rangle.
--   $$
--
--   More explicitly, the left side is the finite sum over $J,K$ and $s,u$ whose factors are
--   $T_JT_K$, the product of deltas outside $s$ and $u$, and $(-M_{J_uK_u})(-M_{J_sK_s})$. This is an internal identity used in the second derivative of the energy form.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L758-L847 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `_private.FunctionalInequalities.Analysis.Tensor.EnergyForm.0.FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum`; the repository is private at upload time).

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

lemma FunctionalInequalities.Analysis.CoordinateTensor.two_slot_sum_408915f (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n, T J * T K *
      (∑ s : Fin r, (∑ u ∈ Finset.univ.erase s,
        (∏ v ∈ (Finset.univ.erase s).erase u, if J v = K v then (1 : ℝ) else 0) *
          (-M (J u) (K u))) * (-M (J s) (K s)))) =
      ∑ s : Fin r, ∑ u ∈ Finset.univ.erase s, inner T (actOn M s (actOn M u T)) := by sorry
