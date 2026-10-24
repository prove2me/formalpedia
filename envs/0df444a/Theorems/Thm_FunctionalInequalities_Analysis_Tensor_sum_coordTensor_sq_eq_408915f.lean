-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_coordTensor_sq_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:05:23.882519+00:00
-- url     : https://prove2.me/theorems/7af10627-5bf6-43e5-8b1d-e1f9535572fa
-- title:
--   Basis Independence of Coordinate Tensor Square Sums
-- statement:
--   This is the basis-independence identity for the squared coefficient sum of a multilinear form.
--
--   Let $E$ be a real inner-product space, let $b$ and $b'$ be orthonormal bases indexed by $\operatorname{Fin}(n)$ and $\operatorname{Fin}(n')$, respectively, and let $\Phi:E^k\to\mathbb R$ be continuous and $k$-linear. Then
--
--   $$\sum_{i:\operatorname{Fin}(k)\to\operatorname{Fin}(n)}\operatorname{coordTensor}_b(\Phi)(i)^2
--   =\sum_{l:\operatorname{Fin}(k)\to\operatorname{Fin}(n')}\operatorname{coordTensor}_{b'}(\Phi)(l)^2.$$
--
--   Thus the squared coordinate-tensor norm is independent of the chosen orthonormal basis, even when the indexing types are presented with different finite cardinalities.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/BasisChange.lean#L68-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.BasisChange`, declaration `FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_408915f {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ∑ i : Fin k → Fin n, coordTensor b Φ i ^ 2 = ∑ l : Fin k → Fin n', coordTensor b' Φ l ^ 2 := by sorry
