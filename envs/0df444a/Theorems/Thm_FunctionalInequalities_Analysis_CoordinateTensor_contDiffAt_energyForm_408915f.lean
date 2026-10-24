-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_contDiffAt_energyForm_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:47.395985+00:00
-- url     : https://prove2.me/theorems/3841a80a-0b32-4e3e-aa12-d3a4ed7f2ca8
-- title:
--   Smoothness of the Energy Form Near Invertible Operators
-- statement:
--   This statement proves that the coordinate-tensor energy form is $C^2$ near an invertible operator.
--
--   Let $n,r\in\mathbb N$, let $A$ be a continuous linear operator on $\mathbb R^n$ represented as `EuclideanSpace ℝ (Fin n)`, and assume $A$ is a unit, hence invertible in the relevant operator ring. Let $T:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$. Then the map
--
--   $$
--   (A',T')\longmapsto \operatorname{energyForm}(A',T')
--   $$
--
--   is twice continuously differentiable at $(A,T)$.
--
--   This local regularity result supplies the differentiability needed for second-order calculations involving the energy form.
--
--   **Formalization Note** The statement uses finite-dimensional `EuclideanSpace ℝ (Fin n)` and Lean's `IsUnit` hypothesis rather than a separately stated determinant condition.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L54-L79 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_EnergyForm
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_SlotAction
import Mathlib

noncomputable section
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

theorem FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_408915f (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsUnit A)
    (T : (Fin r → Fin n) → ℝ) :
    ContDiffAt ℝ 2 (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
      energyForm q.1 q.2) (A, T) := by sorry
