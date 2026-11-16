-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_theorem_5_4
-- name    : NuclearTensor.Membership.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:42:58.045201+00:00
-- url     : https://prove2.me/theorems/b9b47032-011e-48ef-bf9f-b736d217a435
-- title:
--   Theorem 5.4 — classical Hermitian separability
-- statement:
--   For every $\eta>0$, a deterministic algorithm accepts any Hermitian operator $M$ on $(\mathbb C^d)^{\otimes k}$ that is fully separable, and rejects whenever its Frobenius distance from the fully separable density states is at least $\eta$:
--
--   $$M\in\operatorname{Sep}(d,k)\qquad\text{versus}\qquad \operatorname{dist}_F(M,\operatorname{Sep}(d,k))\ge\eta.$$
--
--   Its runtime is $B_\eta d^{C_\eta k}$, uniformly in every positive $d,k$ and every Hermitian input. Positivity, trace one, and an input-norm bound are not assumed. This is the classical separability companion to nuclear-ball membership.
--
--   **Formalization Note** The actual program runs with no local-optimization oracle. The local greatest-eigenvalue optimizer and real Hermitian coordinate conversion must therefore be implemented in finite charged arithmetic/spectral code; their correctness is not an extra hypothesis.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 21, Theorem 5.4; supporting proof in p. 22.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem theorem_5_4 :
    ∀ η : ℝ, 0 < η → ∃ P : Program,
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k → ∀ M : CMat (d ^ k), M.IsHermitian →
        runsWithin σ none A r [] P [d, k] ([η] ++ encodeMatrix M)
          (B * (d : ℝ) ^ (C * k))
          (fun s => ∃ b : Bool, outputsDecision s b ∧ sepDecision η M b) := by sorry

end NuclearTensor.Membership.Supplement
