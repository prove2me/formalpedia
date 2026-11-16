-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_theorem_6_8
-- name    : NuclearTensor.Membership.Supplement.theorem_6_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:47:41.918508+00:00
-- url     : https://prove2.me/theorems/b3fa47b0-ba30-4019-86cb-f90c3a21b041
-- title:
--   Theorem 6.8 — separability from copies
-- statement:
--   For every $\eta>0$, a quantum algorithm given copies of any state $\rho$ on $(\mathbb C^q)^{\otimes k}$ distinguishes
--
--   $$\rho\in\operatorname{Sep}(q,k)\qquad\text{from}\qquad\operatorname{dist}_F(\rho,\operatorname{Sep}(q,k))\ge\eta,$$
--
--   with error at most $1/3$, using $(kq)^{O_\eta(1)}$ time and copies. The constants precede dimensions and the unknown state. This companion theorem supplies the low-dimensional tester needed for the dimension-reduction application.
--
--   **Formalization Note** Accuracy refers to Frobenius distance. The input has copy access only. The short convex mixture, all optimization calls, and final objective estimates must be generated and charged within the finite program; full state tomography is not a free service.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 27, Theorem 6.8; supporting proof in p. 27.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem theorem_6_8 :
    ∀ η : ℝ, 0 < η → ∃ P : QProgram,
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k →
        testerCorrect (d := d) (k := k) P σ A r η (1 / 3)
          (B * (1 + (k : ℝ) * d) ^ C) (B * (1 + (k : ℝ) * d) ^ C) := by sorry

end NuclearTensor.Membership.Supplement
