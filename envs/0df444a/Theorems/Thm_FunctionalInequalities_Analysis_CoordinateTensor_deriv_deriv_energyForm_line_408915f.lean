-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_deriv_deriv_energyForm_line_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:06:41.670663+00:00
-- url     : https://prove2.me/theorems/4fd2fe7e-ded0-460a-8202-9fb50cfded94
-- title:
--   Second Derivative of the Energy Form Along a Line
-- statement:
--   This statement formalizes the second-order energy-form identity associated with (88) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $n,r\in\mathbb N$, let $T,X$ be order-$r$ coordinate tensors on $\mathbb R^n$, and let $H$ be a self-adjoint continuous linear operator on $\mathbb R^n$. Writing $M$ for its standard matrix, define
--
--   $$
--   F(\varepsilon)=\operatorname{energyForm}(I+\varepsilon H,T+\varepsilon X).
--   $$
--
--   Then
--
--   $$
--   F''(0)=2\left(
--   \|X\|^2-2\langle X,\Sigma_M T\rangle
--   +\frac12\|\Sigma_M T\|^2
--   +\frac12\sum_s\|M^{(s)}T\|^2
--   \right).
--   $$
--
--   This is the exact second derivative along the specified line and is used in the tensor energy estimates.
--
--   **Formalization Note** The tensor inner product and norms are the finite coordinate sums defined in Lean; no dimension restriction beyond $n,r\in\mathbb N$ is imposed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L880-L1129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line`; the repository is private at upload time).

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
set_option maxHeartbeats 1600000

theorem FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line_408915f (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (X : (Fin r → Fin n) → ℝ) :
    deriv (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) 0 =
      2 * (inner X X - 2 * inner X (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * inner (actSum (stdMatrix H) T) (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T)) := by sorry
