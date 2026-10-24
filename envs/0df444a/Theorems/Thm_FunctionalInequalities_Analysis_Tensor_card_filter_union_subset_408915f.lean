-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_filter_union_subset_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.card_filter_union_subset_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:00.825722+00:00
-- url     : https://prove2.me/theorems/1cc815e7-5d0f-42c4-ba56-a9fc246ea1ee
-- title:
--   Counting Supersets of Two Fixed Subsets
-- statement:
--   This is a finite-set counting identity for two fixed subsets of equal size.
--
--   Let $\alpha$ be a type with decidable equality, let $U$ be a finite subset of $\alpha$, and let $d$ be a natural number. Assume:
--
--   1. $|U| = 3d$.
--   2. $F$ and $F'$ are $d$-element subsets of $U$.
--
--   Then the number of $2d$-element subsets $E$ of $U$ that contain $F \cup F'$ is
--
--   $$
--   \left|\{E \subseteq U : |E| = 2d \text{ and } F \cup F' \subseteq E\}\right|
--   = \binom{d + |F \cap F'|}{d}.
--   $$
--
--   The statement provides a reusable combinatorial count for supersets of a union of two $d$-element subsets, parameterized by the size of their intersection.
--
--   **Formalization Note** The finite-set families are represented by `Finset.powersetCard` and filtered using `Finset.filter`; the binomial coefficient is `Nat.choose`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L62-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.card_filter_union_subset`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.card_filter_union_subset_408915f (U : Finset α) {d : ℕ} (hU : U.card = 3 * d) {F F' : Finset α}
    (hF : F ∈ U.powersetCard d) (hF' : F' ∈ U.powersetCard d) :
    ((U.powersetCard (2 * d)).filter fun E => F ∪ F' ⊆ E).card =
      (d + (F ∩ F').card).choose d := by sorry
