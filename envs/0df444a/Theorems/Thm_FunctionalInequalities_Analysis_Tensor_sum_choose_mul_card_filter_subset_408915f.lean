-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_choose_mul_card_filter_subset_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:54.597486+00:00
-- url     : https://prove2.me/theorems/f699c10b-7d9d-4e6e-8a77-9b386ba68804
-- title:
--   Vandermonde Count for Subsets of an Intersection
-- statement:
--   This is a finite-set identity expressing a Vandermonde convolution for two fixed subsets.
--
--   Let $\alpha$ be a type with decidable equality, let $U$ be a finite subset of $\alpha$, let $d$ be a natural number, and let $F,F'$ be $d$-element subsets of $U$. For each natural number $s$ from $0$ through $d$, count the $s$-element subsets $S$ of $U$ satisfying $S \subseteq F \cap F'$. Then
--
--   $$
--   \sum_{s=0}^{d} \binom{d}{s}
--   \left|\{S \subseteq U : |S|=s \text{ and } S \subseteq F \cap F'\}\right|
--   = \binom{d+|F \cap F'|}{d}.
--   $$
--
--   This identity is a reusable combinatorial summation formula, with the summands counting subsets of the intersection and weighting them by binomial coefficients.
--
--   **Formalization Note** The summation is implemented over `Finset.range (d + 1)`, and the counted families use `Finset.powersetCard` followed by `Finset.filter`; binomial coefficients are represented by `Nat.choose`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L194-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.sum_choose_mul_card_filter_subset_408915f (U : Finset α) {d : ℕ} {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ∑ s ∈ range (d + 1), d.choose s * ((U.powersetCard s).filter fun S => S ⊆ F ∩ F').card =
      (d + (F ∩ F').card).choose d := by sorry
