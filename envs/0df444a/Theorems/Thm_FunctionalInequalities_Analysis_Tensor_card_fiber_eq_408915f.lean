-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_fiber_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.card_fiber_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:02.227016+00:00
-- url     : https://prove2.me/theorems/fd1b515d-d2f7-4b68-b3a3-f9da3d2bbca3
-- title:
--   Equal Fiber Cardinalities for Block Images
-- statement:
--   This is a finite-combinatorial fiber-counting lemma.
--
--   Let $\Omega$ be finite and let $A,Q,F,F'\subseteq\Omega$ be finite subsets. Assume that $F$ and $F'$ are both $|A|$-element subsets of $Q$. Then the two fibers of the map $\sigma\mapsto\sigma(A)$, restricted to permutations fixing every point outside $Q$, have equal cardinality:
--
--   $$
--   \#\{\sigma\text{ fixing outside }Q:\sigma(A)=F\}
--   =
--   \#\{\sigma\text{ fixing outside }Q:\sigma(A)=F'\}.
--   $$
--
--   This uniformity is used when grouping permutation sums by the image of $A$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L769-L804 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.card_fiber_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.card_fiber_eq_408915f {A Q : Finset Ω} {F F' : Finset Ω}
    (hF : F ∈ Q.powersetCard A.card) (hF' : F' ∈ Q.powersetCard A.card) :
    ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F).card =
      ((fixingOutside Q).filter fun σ : Equiv.Perm Ω => A.image σ = F').card := by sorry
