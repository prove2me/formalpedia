-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_theorem_6_1
-- name    : NuclearTensor.Membership.Supplement.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:47:10.74087+00:00
-- url     : https://prove2.me/theorems/e1837afe-99eb-4d24-8802-8ea928947e55
-- title:
--   Theorem 6.1 — signed product-state optimization
-- statement:
--   An unknown $k$-party state $\rho$ of local dimension $q$ is supplied by copies. The explicitly supplied state $\sigma=\sum_{\ell=1}^T w_\ell\bigotimes_j\sigma_{\ell,j}$ is a normalized convex mixture: $w_\ell\ge0$, $\sum_\ell w_\ell=1$, and every factor is a density matrix. For every $\eta,\delta>0$, a quantum algorithm outputs classical unit vectors $x_1^*,\ldots,x_k^*$ such that, with probability at least $1-\delta$,
--
--   $$\operatorname{Tr}((\rho-\sigma)\bigotimes_j|x_j^*\rangle\langle x_j^*|)\ge\max_{\|x_j\|=1}\operatorname{Tr}((\rho-\sigma)\bigotimes_j|x_j\rangle\langle x_j|)-\eta^2.$$
--
--   Time and copies are $\operatorname{poly}_\eta(kqT L(\delta))$. This signed optimizer is a companion theorem and provides the oracle implemented within the copy-access membership algorithm.
--
--   **Formalization Note** With $\theta=\min(\eta^2/8,1)$, the proof uses a $\theta/2$-cover, LocalSearch parameters $\alpha=(\theta/16)^4$, $\epsilon=\theta/16$, and candidate-estimation errors at most $\theta/16$. The small-optimum branch loses at most $9\eta^2/64$, so $\eta^2$ is a concrete source-valid realization of $O(\eta^2)$. Random product-basis candidates handle that branch and an empty cover; no empty argmax is required. All confidence is shared across adaptive calls and estimates.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: positive failure parameters and logarithmic confidence factors → all positive failure parameters, using L(x)=1+max(0,log(1/x)) in resource bounds; reason: agrees with logarithmic confidence scaling in the nontrivial range and accommodates the vacuous-success branch for x at least one
--   - encoding: objective loss O(eta^2) → objective loss at most eta^2; reason: the source parameters and candidate errors give at most 9eta^2/64 in the nontrivial branch; above the objective diameter any unit product suffices
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 22, Theorem 6.1; supporting proof in pp. 26–27.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem theorem_6_1 :
    ∀ η : ℝ, 0 < η → ∃ P : QProgram,
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k T : ℕ, 0 < d → 0 < k → ∀ δ : ℝ, 0 < δ →
      ∀ S : Mixture d k T, ∀ ρ : CMat (d ^ k), IsDensity ρ →
        quantumAlgorithm ρ σ A r P [d, k, T] ([η, δ] ++ encodeMixture S)
          (B * (1 + (k : ℝ) * d * (1 + T) * confidence δ) ^ C)
          (B * (1 + (k : ℝ) * d * (1 + T) * confidence δ) ^ C) δ
          (signedOutput ρ S η) (returnsProduct d k) := by sorry

end NuclearTensor.Membership.Supplement
