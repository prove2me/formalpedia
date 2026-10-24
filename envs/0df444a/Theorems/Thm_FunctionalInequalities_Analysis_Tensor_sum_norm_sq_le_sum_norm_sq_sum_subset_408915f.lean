-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_le_sum_norm_sq_sum_subset_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:55.023061+00:00
-- url     : https://prove2.me/theorems/3f05cc19-387a-4793-bce8-ff9e0d25c594
-- title:
--   Subset-Sum Norm Inequality
-- statement:
--   This is the inequality form of the BKL subset-sum estimate.
--
--   Let $V$ be a real inner-product space, let $U$ be finite with $|U|=3d$, and let $x_F\in V$ be assigned to every $d$-element subset $F\subseteq U$. Then
--
--   $$
--   \sum_{\substack{F\subseteq U\\|F|=d}}\|x_F\|^2
--   \le
--   \sum_{\substack{E\subseteq U\\|E|=2d}}
--   \left\|\sum_{\substack{F\subseteq E\\|F|=d}}x_F\right\|^2.
--   $$
--
--   This inequality is the norm estimate extracted from the exact subset-sum identity and is used in the representation-theoretic symmetrization bound.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L399-L458 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
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
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section SubsetSum
variable {α : Type*} [DecidableEq α]

theorem FunctionalInequalities.Analysis.Tensor.sum_norm_sq_le_sum_norm_sq_sum_subset_408915f (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ F ∈ U.powersetCard d, ‖x F‖ ^ 2 ≤
      ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 := by sorry
