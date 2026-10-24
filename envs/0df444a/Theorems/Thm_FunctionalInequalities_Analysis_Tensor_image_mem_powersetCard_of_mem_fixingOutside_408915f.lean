-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_image_mem_powersetCard_of_mem_fixingOutside_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:01.026508+00:00
-- url     : https://prove2.me/theorems/001d7a4c-1ddb-467b-b04b-f04938c5ffb6
-- title:
--   Images of Subsets Under Supported Permutations
-- statement:
--   This is a finite-set invariance lemma.
--
--   Let $A,Q\subseteq\Omega$ be finite subsets with $A\subseteq Q$. If a permutation $\sigma$ fixes every point outside $Q$, then the image $\sigma(A)$ is a subset of $Q$ with the same cardinality as $A$:
--
--   $$
--   \sigma(A)\in\{F\subseteq Q:|F|=|A|\}.
--   $$
--
--   This identifies the possible images of $A$ when permutation sums are restricted to permutations supported in $Q$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L716-L730 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.image_mem_powersetCard_of_mem_fixingOutside_408915f {A Q : Finset Ω} (hAQ : A ⊆ Q)
    {σ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside Q) : A.image σ ∈ Q.powersetCard A.card := by sorry
