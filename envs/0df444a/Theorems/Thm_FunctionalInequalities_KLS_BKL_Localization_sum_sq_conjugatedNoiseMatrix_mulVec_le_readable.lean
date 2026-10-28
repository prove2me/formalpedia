-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_sum_sq_conjugatedNoiseMatrix_mulVec_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.sum_sq_conjugatedNoiseMatrix_mulVec_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:49.401188+00:00
-- url     : https://prove2.me/theorems/bd7bc76e-3a86-4f3a-8622-a29d176bc214
-- title:
--   Conjugated Noise Matrix Vector Bound
-- statement:
--   This formalizes the conjugated form of BKL (79), p. 24.
--
--   Let $\mu$ be a compactly supported isotropic log-concave probability measure on $\mathbb{R}^n$. Assume the compact cumulant bound `CumulantBoundCompact 2 8`. Let $p=(c,Q)$ be a localization parameter such that $Q$ is self-adjoint and positive semidefinite, and let $v:\operatorname{Fin}(n)\to\mathbb{R}$. Then
--
--   $$
--   \sum_{i,a}\left(\sum_b
--   \widetilde H_i(a,b)v_b\right)^2
--   \le 8\sum_a v_a^2,
--   $$
--
--   where $\widetilde H_i$ is represented by `conjugatedNoiseMatrix μ hc p i`.
--
--   This is the coordinate-vector estimate underlying the Hilbert–Schmidt and Lyapunov generator bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_sq_conjugatedNoiseMatrix_mulVec_le (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
--       (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
--       (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) (v : Fin n → ℝ) :
--       ∑ i, ∑ a, (∑ b, conjugatedNoiseMatrix μ hc p i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/NoiseBound`](https://prove2.me/theorems/f9dd651e-3cbd-4d7a-892b-a8785e460e72).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Supporting theorems: [`inner_self_pos_of_isPositive_of_isUnit`](https://prove2.me/theorems/8f74694a-1776-48f4-8eff-687b9d5a92eb), [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`compactPosterior_cumulant_bound`](https://prove2.me/theorems/dafbeb46-ce93-4b8d-bf8b-6a64738b3ea3), [`cumulant_middle_sum`](https://prove2.me/theorems/9e0a41d8-8c46-4618-8921-3e596dfd076a).
--
--   Previous: [`cumulantEnergy_succ_eq`](https://prove2.me/theorems/a8033ec2-2b13-4f3a-8086-a0cc4a62b333).
--
--   [Source excerpt, lines 199–202](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L199-L202) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 5.1, p. 22. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean#L196-L361 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.NoiseBound`, declaration `FunctionalInequalities.KLS.BKL.Localization.sum_sq_conjugatedNoiseMatrix_mulVec_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound

open scoped RealInnerProductSpace
variable {n : ℕ}
variable (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.sum_sq_conjugatedNoiseMatrix_mulVec_le_readable (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    (h8 : LogConcave.Suspension.CumulantBoundCompact 2 8) (p : Param n)
    (hSym : IsSelfAdjoint p.2) (hQ : ∀ x, 0 ≤ ⟪p.2 x, x⟫) (v : Fin n → ℝ) :
    ∑ i, ∑ a, (∑ b, conjugatedNoiseMatrix μ hc p i a b * v b) ^ 2 ≤ 8 * ∑ a, v a ^ 2 := by sorry
