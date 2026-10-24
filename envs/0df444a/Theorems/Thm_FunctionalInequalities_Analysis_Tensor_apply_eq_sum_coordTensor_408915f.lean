-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_apply_eq_sum_coordTensor_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:24.259786+00:00
-- url     : https://prove2.me/theorems/5662f6b6-68ba-49f2-8847-74eb9a322054
-- title:
--   Orthonormal Basis Expansion of a Multilinear Form
-- statement:
--   This is the coordinate expansion of a real continuous multilinear form.
--
--   Let $E$ be a real inner-product space, let $b$ be an orthonormal basis indexed by $\operatorname{Fin}(n)$, let $\Phi:E^k\to\mathbb R$ be a continuous $k$-linear map, and let $h_0,\ldots,h_{k-1}\in E$. Then
--
--   $$\Phi(h_0,\ldots,h_{k-1})
--   =\sum_{i:\operatorname{Fin}(k)\to\operatorname{Fin}(n)}\operatorname{coordTensor}_b(\Phi)(i)\prod_{j=0}^{k-1}\langle b(i_j),h_j\rangle.$$
--
--   The formula expresses a multilinear form through its coordinate tensor in an orthonormal basis.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L107-L125 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coefficients`, declaration `FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_408915f {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (h : Fin k → E) :
    Φ h = ∑ i : Fin k → Fin n, coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by sorry
