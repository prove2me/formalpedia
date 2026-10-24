-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_apply_eq_of_image_eq_408915f
-- name    : FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:09:01.396856+00:00
-- url     : https://prove2.me/theorems/9d5eec8d-c68c-4b43-9da3-b368a0766ee6
-- title:
--   Representation Values Depend Only on the Image of a Block
-- statement:
--   This is a group-theoretic auxiliary lemma for partial symmetrization.
--
--   Let $\Omega$ be a finite type, let $V$ be a real inner-product space, and let $\rho$ be a monoid homomorphism from permutations of $\Omega$ to linear isometric equivalences of $V$. Let $A,B\subseteq\Omega$ be finite subsets, let $v\in V$, and suppose:
--   1. $\rho(\sigma)v=v$ for every permutation $\sigma$ fixing every point outside $A$.
--   2. $\rho(\sigma)v=v$ for every permutation $\sigma$ fixing every point outside $B$.
--   3. $\sigma$ and $\tau$ both fix every point outside $A\cup B$.
--   4. $\sigma(A)=\tau(A)$.
--
--   Then
--
--   $$
--   \rho(\sigma)v=\rho(\tau)v.
--   $$
--
--   The lemma shows that, under the two invariance assumptions, the represented vector depends only on the image of $A$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L604-L714 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq_408915f (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B : Finset Ω} (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v)
    {σ τ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside (A ∪ B)) (hτ : τ ∈ fixingOutside (A ∪ B))
    (h : A.image σ = A.image τ) : ρ σ v = ρ τ v := by sorry
