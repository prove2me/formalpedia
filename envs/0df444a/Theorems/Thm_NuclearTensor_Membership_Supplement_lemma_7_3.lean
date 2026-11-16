-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_lemma_7_3
-- name    : NuclearTensor.Membership.Supplement.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:49:03.590205+00:00
-- url     : https://prove2.me/theorems/f4449dc1-c923-44af-9c26-4328194f74ed
-- title:
--   Lemma 7.3 — local spectral filtering
-- statement:
--   For an unknown $k$-party state $\rho$ of local dimension $d$, let $A_j=\operatorname{Tr}_{-j}(\rho^2)$, $F_j=f_a(A_j)$, and $a=2048k^2/\eta^4$. The ramp is zero up to $1/a$, equals $at-1$ between $1/a$ and $2/a$, and is one from $2/a$ onward. For every $\eta,\delta>0$, a routine implements
--
--   $$\Phi_j(X)=F_jXF_j+\operatorname{Tr}((I-F_j^2)X)|\perp\rangle\langle\perp|$$
--
--   on a specified target register with trace-norm channel error at most $\delta$, even with an arbitrary entangled reference. It uses $\operatorname{poly}(k,\eta^{-1},\delta^{-1})$ fresh auxiliary copies and $\operatorname{poly}(k,\eta^{-1},\delta^{-1},\ell(d))$ time. This supports the dimensionality-reduction companion theorem.
--
--   **Formalization Note** The flag is an extra orthogonal dimension; the successful and flagged blocks together are trace preserving. The unknown filter is defined spectrally but is not an executable primitive. The approximating program accesses $\rho$ only by fresh copies.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - reading: cutoff f_Theta(k^2/eta^4) → cutoff a=2048k^2/eta^4 from the proof on page 31; reason: fixes the source proof parameter without changing either promise or any resource dependence
--   - encoding: logarithmic dimension factors → ell(d)=1+ceil(log_2 d); reason: the usual positive input-size convention includes one-dimensional systems without a zero runtime bound
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 30, Lemma 7.3; supporting proof in pp. 46–48.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem lemma_7_3 :
    ∃ P : QProgram, ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k → ∀ η δ : ℝ, 0 < η → 0 < δ →
      ∀ j : Fin k, ∀ ρ : CMat (d ^ k), IsDensity ρ →
        implements ρ σ A r P [d, k, j.val] [η, δ]
          (flagged (localFilter ρ η j)) δ
          (B * ((k : ℝ) + inverseScale η + inverseScale δ) ^ C)
          (B * ((k : ℝ) + inverseScale η + inverseScale δ + logSize d) ^ C) := by sorry

end NuclearTensor.Membership.Supplement
