-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_subset_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:56.960331+00:00
-- url     : https://prove2.me/theorems/a59d7467-e52b-47bb-910c-2e080ca4d2d1
-- title:
--   BKL Subset-Sum Identity
-- statement:
--   This formalizes the equality in (25) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Lemma 2.2, p. 9.
--
--   Let $V$ be a real inner-product space, let $U$ be a finite set with $|U|=3d$, and let $x_F\in V$ be assigned to every $d$-element subset $F\subseteq U$. Then
--
--   $$
--   \sum_{\substack{E\subseteq U\\|E|=2d}}
--   \left\|\sum_{\substack{F\subseteq E\\|F|=d}}x_F\right\|^2
--   =
--   \sum_{s=0}^{d}\binom ds
--   \sum_{\substack{S\subseteq U\\|S|=s}}
--   \left\|\sum_{\substack{F\subseteq U,\ |F|=d\\S\subseteq F}}x_F\right\|^2.
--   $$
--
--   This is the central combinatorial norm identity used in the partial symmetrization estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L272-L397 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq_408915f (U : Finset α) {d : ℕ} (hU : U.card = 3 * d)
    (x : Finset α → V) :
    ∑ E ∈ U.powersetCard (2 * d), ‖∑ F ∈ E.powersetCard d, x F‖ ^ 2 =
      ∑ s ∈ range (d + 1), (d.choose s : ℝ) *
        ∑ S ∈ U.powersetCard s, ‖∑ F ∈ (U.powersetCard d).filter (S ⊆ ·), x F‖ ^ 2 := by sorry
