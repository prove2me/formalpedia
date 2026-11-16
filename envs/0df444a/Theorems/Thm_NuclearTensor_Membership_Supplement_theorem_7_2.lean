-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_theorem_7_2
-- name    : NuclearTensor.Membership.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:51:54.348386+00:00
-- url     : https://prove2.me/theorems/e6148c42-825d-4888-93a2-2063cc04ef52
-- title:
--   Theorem 7.2 — dimension-independent copy complexity
-- statement:
--   For every $\eta>0$, a quantum algorithm given copies of any unknown state $\rho$ on $(\mathbb C^d)^{\otimes k}$ distinguishes
--
--   $$\rho\in\operatorname{Sep}(d,k)\qquad\text{from}\qquad\operatorname{dist}_F(\rho,\operatorname{Sep}(d,k))\ge\eta,$$
--
--   with error at most $1/3$, using $k^{O_\eta(1)}$ copies and total time $(k\ell(d))^{O_\eta(1)}$. Copy complexity is independent of local dimension. This companion theorem combines the low-dimensional test with dimensionality reduction.
--
--   **Formalization Note** All positive $d,k$ are retained, with $\ell(d)=1+\lceil\log_2d\rceil$. The proof uses the direct low-dimensional tester when the chosen reduction dimension exceeds $d$, and amplifies its error from $1/3$ to $1/10$ before applying Theorem 7.1. The unknown local embeddings are never supplied as classical input.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: logarithmic dimension factors → ell(d)=1+ceil(log_2 d); reason: the usual positive input-size convention includes one-dimensional systems without a zero runtime bound
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 28, Theorem 7.2; supporting proof in pp. 27–28.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem theorem_7_2 :
    ∀ η : ℝ, 0 < η → ∃ P : QProgram,
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k →
        testerCorrect (d := d) (k := k) P σ A r η (1 / 3)
          (B * (k : ℝ) ^ C) (B * ((k : ℝ) * logSize d) ^ C) := by sorry

end NuclearTensor.Membership.Supplement
