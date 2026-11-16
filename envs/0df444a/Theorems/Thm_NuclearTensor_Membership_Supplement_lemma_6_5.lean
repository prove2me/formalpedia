-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_lemma_6_5
-- name    : NuclearTensor.Membership.Supplement.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:44:18.223983+00:00
-- url     : https://prove2.me/theorems/3311b9d2-4da5-4fc6-8d16-8996318b72aa
-- title:
--   Lemma 6.5 — subspace tomography
-- statement:
--   Let $\omega$ be an unknown $m$-party state of local dimension $q$. A known subspace $V$ has an explicitly supplied orthonormal product basis $a_1,\ldots,a_D$, with projector $P=\sum_\ell|a_\ell\rangle\langle a_\ell|$. For every $\epsilon,\delta>0$, a quantum algorithm outputs a classical operator $\widehat\omega$ supported on $V$, with
--
--   $$\Pr\{\|\widehat\omega-P\omega P\|_F\le\epsilon\}\ge1-\delta.$$
--
--   It uses at most $B D^2\epsilon^{-2}L(\delta)$ copies and total time polynomial in $m,q,D,\epsilon^{-1},L(\delta)$. This is the subspace-tomography support for LocalSearch and Theorem 6.1.
--
--   **Formalization Note** The classical output is a $D\times D$ coefficient matrix in the given basis, so an exponential ambient matrix is not written. At $D=0$ this represents the zero operator and requires no copies.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: positive failure parameters and logarithmic confidence factors → all positive failure parameters, using L(x)=1+max(0,log(1/x)) in resource bounds; reason: agrees with logarithmic confidence scaling in the nontrivial range and accommodates the vacuous-success branch for x at least one
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 23, Lemma 6.5; supporting proof in p. 38.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem lemma_6_5 :
    ∃ P : QProgram, ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d m D : ℕ, 0 < d → 0 < m → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∀ V : ProductSubspace d m D, ∀ ω : CMat (d ^ m), IsDensity ω →
        quantumAlgorithm ω σ A r P [d, m, D] ([ε, δ] ++ V.encode)
          (B * (D : ℝ) ^ 2 * ε⁻¹ ^ 2 * confidence δ)
          (B * (1 + m + d + D + ε⁻¹ + confidence δ) ^ C) δ
          (tomographyOutput ω V ε) (returnsMatrix D) := by sorry

end NuclearTensor.Membership.Supplement
