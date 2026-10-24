-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_hasDerivAt_energyForm_line_408915f
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:07:59.344091+00:00
-- url     : https://prove2.me/theorems/b6deeeba-8b15-44ca-ac5e-9b1dd5c98454
-- title:
--   Directional Derivative of the Tensor Energy Form
-- statement:
--   This is a first-order directional derivative formula for the coordinate-tensor energy form.
--
--   Let $n,r\in\mathbb{N}$. Let $T,X:(\mathrm{Fin}\,r\to\mathrm{Fin}\,n)\to\mathbb{R}$, and let $H$ be a continuous linear map from $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$ to itself. Writing `energyForm` for the energy functional, `inner` for the tensor inner product, `stdMatrix H` for the standard matrix of $H$, and `actSum` for its induced tensor action, the derivative at $\varepsilon=0$ of
--
--   $$\varepsilon\mapsto \operatorname{energyForm}(1+\varepsilon H,T+\varepsilon X)$$
--
--   is
--
--   $$2\,\langle T,X\rangle-\left\langle T,\operatorname{actSum}(\operatorname{stdMatrix}(H),T)\right\rangle.$$
--
--   This technical line-derivative identity can be reused in first-order variations of tensor energy expressions.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L293-L385 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line`; the repository is private at upload time).

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
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.CoordinateTensor.hasDerivAt_energyForm_line_408915f (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    HasDerivAt (fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X))
      (2 * inner T X - inner T (actSum (stdMatrix H) T)) 0 := by sorry
