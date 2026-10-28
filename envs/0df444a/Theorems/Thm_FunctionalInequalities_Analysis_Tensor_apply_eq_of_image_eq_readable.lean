-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_apply_eq_of_image_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:59.117104+00:00
-- url     : https://prove2.me/theorems/d208003e-b651-43c5-a3e4-e5c080e8a606
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem apply_eq_of_image_eq (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B : Finset Ω} (v : V)
--       (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v)
--       {σ τ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside (A ∪ B)) (hτ : τ ∈ fixingOutside (A ∪ B))
--       (h : A.image σ = A.image τ) : ρ σ v = ρ τ v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Previous: [`exists_mem_fixingOutside_image_eq`](https://prove2.me/theorems/14b5df8e-d013-4b01-a20c-a437a2621fc7) · Next: [`image_mem_powersetCard_of_mem_fixingOutside`](https://prove2.me/theorems/7bccdbf5-5ef4-4af0-ab13-ffd9fefe2d80).
--
--   [Source excerpt, lines 606–609](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L606-L609) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L604-L714 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Analysis.Tensor.apply_eq_of_image_eq_readable (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) {A B : Finset Ω} (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v)
    {σ τ : Equiv.Perm Ω} (hσ : σ ∈ fixingOutside (A ∪ B)) (hτ : τ ∈ fixingOutside (A ∪ B))
    (h : A.image σ = A.image τ) : ρ σ v = ρ τ v := by sorry
