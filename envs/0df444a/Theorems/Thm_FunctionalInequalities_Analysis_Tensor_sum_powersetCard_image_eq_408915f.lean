-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_powersetCard_image_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:10:54.412128+00:00
-- url     : https://prove2.me/theorems/42d31631-5d5e-444e-9e9f-1a7891e50863
-- title:
--   Equivariance of Subset Sums
-- statement:
--   This is an equivariance identity for subset sums.
--
--   Let $\Omega$ be a type, let $V$ be a real inner-product space, let $\rho$ be a permutation representation by linear isometries, let $g$ be a permutation, and let $T$ assign a vector $T(F)$ to each finite subset $F$. Assume
--
--   $$
--   \rho(g)T(F)=T(g(F))
--   $$
--
--   for every finite subset $F$. Then for every finite subset $Q$ and natural number $k$,
--
--   $$
--   \sum_{\substack{F\subseteq g(Q)\\|F|=k}}T(F)
--   =\rho(g)\left(\sum_{\substack{F\subseteq Q\\|F|=k}}T(F)\right).
--   $$
--
--   The result permits subset sums over different blocks to be compared by applying a representing permutation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L907-L928 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq`; the repository is private at upload time).

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
omit [Fintype Ω]

theorem FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_408915f (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (g : Equiv.Perm Ω)
    (T : Finset Ω → V) (hT : ∀ F, ρ g (T F) = T (F.image g)) (Q : Finset Ω) (k : ℕ) :
    ∑ F ∈ (Q.image g).powersetCard k, T F = ρ g (∑ F ∈ Q.powersetCard k, T F) := by sorry
