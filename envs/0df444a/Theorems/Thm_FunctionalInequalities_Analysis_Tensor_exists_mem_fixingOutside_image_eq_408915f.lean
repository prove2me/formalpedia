-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_mem_fixingOutside_image_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:00.361202+00:00
-- url     : https://prove2.me/theorems/2b999d5a-9659-4f73-ae0d-92e4c726eb55
-- title:
--   Permutation Matching Equal-Size Subsets Inside a Finite Set
-- statement:
--   This is a finite-combinatorial auxiliary lemma.
--
--   Let $\Omega$ be finite and let $s,t,W\subseteq\Omega$ be finite subsets. Assume $s\subseteq W$, $t\subseteq W$, and $|s|=|t|$. Then there exists a permutation $\sigma$ of $\Omega$ such that $\sigma$ fixes every point outside $W$ and
--
--   $$
--   \sigma(s)=t.
--   $$
--
--   The result supplies the permutation used to compare fibers of the image map on permutations supported inside $W$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L462-L602 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_408915f {W s t : Finset Ω} (hs : s ⊆ W) (ht : t ⊆ W)
    (hst : s.card = t.card) : ∃ σ ∈ fixingOutside W, s.image σ = t := by sorry
