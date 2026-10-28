-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_norm_le_four_pow_mul_norm_blockAverage_readable
-- name    : FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_blockAverage_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:09.873451+00:00
-- url     : https://prove2.me/theorems/9105d9b3-66ee-4045-906c-b84556304fa1
-- title:
--   Four-Power Partial Symmetrization Bound
-- statement:
--   Let $\Omega$ be finite, let $V$ be a real inner-product space, and let $\rho$ be a permutation representation by linear isometries. Let $A,B,Q\subseteq\Omega$ and $d\in\mathbb N$ satisfy:
--   1. $|A|=d$ and $|B|=2d$.
--   2. $A$ and $B$ are disjoint.
--   3. $A\subseteq Q\subseteq A\cup B$.
--   4. $|Q|=2d$.
--   5. $v$ is invariant under permutations fixing outside $A$ and under permutations fixing outside $B$.
--
--   Then
--
--   $$
--   \|v\|\le 4^d\,\|\operatorname{blockAverage}(\rho,Q,v)\|.
--   $$
--
--   This is the representation-level form of the partial symmetrization estimate with the universal elementary factor $4^d$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_le_four_pow_mul_norm_blockAverage (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
--       {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
--       (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
--       (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
--       ‖v‖ ≤ (4 : ℝ) ^ d * ‖blockAverage ρ Q v‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Supporting theorems: [`norm_le_choose_mul_norm_blockAverage`](https://prove2.me/theorems/ce21f420-f15e-4872-8c85-4a342b34288d).
--
--   Previous: [`norm_le_choose_mul_norm_blockAverage`](https://prove2.me/theorems/ce21f420-f15e-4872-8c85-4a342b34288d).
--
--   [Source excerpt, lines 1114–1118](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L1114-L1118) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Lemma 2.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), p. 9.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 2.2, p. 9. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L1113-L1129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_blockAverage`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_blockAverage_readable (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V))
    {A B Q : Finset Ω} {d : ℕ} (hA : A.card = d) (hB : B.card = 2 * d) (hAB : Disjoint A B)
    (hAQ : A ⊆ Q) (hQ : Q ⊆ A ∪ B) (hQc : Q.card = 2 * d) (v : V)
    (hvA : ∀ σ ∈ fixingOutside A, ρ σ v = v) (hvB : ∀ σ ∈ fixingOutside B, ρ σ v = v) :
    ‖v‖ ≤ (4 : ℝ) ^ d * ‖blockAverage ρ Q v‖ := by sorry
