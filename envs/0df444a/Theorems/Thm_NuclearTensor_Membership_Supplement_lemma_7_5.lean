-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_lemma_7_5
-- name    : NuclearTensor.Membership.Supplement.lemma_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:50:56.821938+00:00
-- url     : https://prove2.me/theorems/d73e86c8-c8fd-4a75-87ca-c8b0d5ad9e2c
-- title:
--   Lemma 7.5 — universal Schur compression
-- statement:
--   For every $D\ge q>0$ and copy count $N\ge0$, there is a channel $C_{D\to q}^{(N)}$ depending only on $D,q,N$. For every finite reference $B$, isometry $V:\mathbb C^q\to\mathbb C^D$, and joint state $X$ on $(\mathbb C^q)^{\otimes N}\otimes B$,
--
--   $$((T_q^{(N)}\circ C_{D\to q}^{(N)})\otimes I_B)((V^{\otimes N}\otimes I_B)X((V^\dagger)^{\otimes N}\otimes I_B))=(T_q^{(N)}\otimes I_B)(X),$$
--
--   where $T_q^{(N)}(Y)=\int U^{\otimes N}Y(U^\dagger)^{\otimes N}\,dU$ uses normalized Haar measure. For every $\delta>0$, this channel has a $\delta$-accurate implementation in time $\operatorname{poly}(N,q,\ell(D),L(\delta))$ and uses no additional input copies. This is the compression support for Theorem 7.1.
--
--   **Formalization Note** The exact channel is existential as in the source lemma. The implementation must be finite elementary-gate code and is compared in trace norm with arbitrary entangled references. The identity preserves the common-unitary average and all reference correlations; it does not recover $X$ or learn $V$. The scalar empty tensor power handles $N=0$.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: positive failure parameters and logarithmic confidence factors → all positive failure parameters, using L(x)=1+max(0,log(1/x)) in resource bounds; reason: agrees with logarithmic confidence scaling in the nontrivial range and accommodates the vacuous-success branch for x at least one
--   - encoding: logarithmic dimension factors → ell(d)=1+ceil(log_2 d); reason: the usual positive input-size convention includes one-dimensional systems without a zero runtime bound
--   - encoding: N-fold tensor powers and arbitrary finite references → scalar empty tensor power for N=0 and reference dimensions Fin R, with the exact identity for every normalized left-invariant Borel Haar measure; reason: all finite Hilbert reference systems have these coordinates; Haar existence is asserted, and the common-unitary average is unchanged
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 31, Lemma 7.5; supporting proof in pp. 49–51.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem lemma_7_5 :
    ∃ (channels : (D q N : ℕ) → CMat (D ^ N) → CMat (q ^ N)) (P : QProgram),
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ D q N : ℕ, 0 < q → q ≤ D →
        schurIdentity (channels D q N) ∧ ∀ δ : ℝ, 0 < δ →
          implements dummyState σ A r P [D, q, N] [δ] (channels D q N) δ 0
            (B * (1 + N + q + logSize D + confidence δ) ^ C) := by sorry

end NuclearTensor.Membership.Supplement
