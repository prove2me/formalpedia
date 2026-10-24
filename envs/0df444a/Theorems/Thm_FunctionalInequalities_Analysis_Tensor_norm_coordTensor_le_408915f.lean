-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_coordTensor_le_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:43.425704+00:00
-- url     : https://prove2.me/theorems/9a62ab3a-3075-4cfa-91b2-b04010643d3f
-- title:
--   Coordinate Tensor Norm Bound
-- statement:
--   This theorem bounds the coordinate-array norm of a multilinear map in an orthonormal basis.
--
--   Let $E$ be a real inner-product space, let $n,k\in\mathbb N$, let $b$ be an orthonormal basis indexed by $\operatorname{Fin}(n)$, and let $\Phi:E^k\to\mathbb R$ be a continuous $k$-linear map. Then its coordinate tensor satisfies
--
--   $$\|\operatorname{coordTensor}(b,\Phi)\|\le (\sqrt n)^k\,\|\Phi\|.$$
--
--   Here `coordTensor` is the coefficient array obtained by evaluating $\Phi$ on basis vectors, while $\|\Phi\|$ is the continuous multilinear operator norm. The estimate is a dimension-dependent bridge from operator norms to coordinate Hilbert-space norms.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L180-L213 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coefficients`, declaration `FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Coordinate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Multilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
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
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le_408915f {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ‖coordTensor b Φ‖ ≤ Real.sqrt n ^ k * ‖Φ‖ := by sorry
