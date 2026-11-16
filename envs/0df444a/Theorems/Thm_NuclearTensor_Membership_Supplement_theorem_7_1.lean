-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_theorem_7_1
-- name    : NuclearTensor.Membership.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:51:26.820396+00:00
-- url     : https://prove2.me/theorems/0a4185cd-d991-4381-b5ad-4e194da03e38
-- title:
--   Theorem 7.1 — black-box dimension reduction
-- statement:
--   For every $\eta>0$ and positive $d,k$, choose $q=\max(1,\lceil2048k^2/\eta^4\rceil)$ and assume $q\le d$. Every supplied $N$-copy tester on $(\mathbb C^q)^{\otimes k}$ with gap $\eta/2$, error at most $1/10$, and time $T$ yields a tester on $(\mathbb C^d)^{\otimes k}$ with gap $\eta$ and error at most $1/3$:
--
--   $$\rho\in\operatorname{Sep}(d,k)\qquad\text{versus}\qquad\operatorname{dist}_F(\rho,\operatorname{Sep}(d,k))\ge\eta.$$
--
--   Copies are $\operatorname{poly}(k,N,\eta^{-1})$ and total time is $T+\operatorname{poly}(k,N,\eta^{-1},\ell(d))$. The overhead constants do not depend on the supplied tester, $T$, $d$, or the unknown state. This is the dimensionality-reduction companion theorem.
--
--   **Formalization Note** The supplied tester is actual finite code on the $N$-copy input, not a state or correctness oracle. A charged tail call runs it at most once. The cutoff includes the flag dimension because $\operatorname{rank}(F_j)<a$. Estimation error $\eta^2/(128k)$ and rejection threshold $3\eta^2/(64k)$ give nonrejection loss at most $\sqrt{7/32}\eta<\eta/2$. Allocate at most $1/30$ each to estimation failure, filtering, compression, and Haar implementation; including tester error gives $7/30<1/3$. The far case is empty above the density-state Frobenius diameter.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - reading: cutoff f_Theta(k^2/eta^4) → cutoff a=2048k^2/eta^4 from the proof on page 31; reason: fixes the source proof parameter without changing either promise or any resource dependence
--   - reading: the reduction chooses q=O(k^2/eta^4) with q at most d → q=max(1,ceil(2048k^2/eta^4)), with q at most d; reason: rounding includes the flag; the bound is O(k^2/eta^4) in the nontrivial gap range and larger gaps have no far states
--   - encoding: logarithmic dimension factors → ell(d)=1+ceil(log_2 d); reason: the usual positive input-size convention includes one-dimensional systems without a zero runtime bound
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 28, Theorem 7.1; supporting proof in pp. 31–35.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem theorem_7_1 :
    ∃ R : QProgram, ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ η : ℝ, 0 < η → ∀ d k : ℕ, 0 < d → 0 < k →
      let q := reducedDimension k η
      q ≤ d → ∀ N T : ℕ, ∀ P : QProgram,
        testerOnCopies (d := q) (k := k) P σ A r N (η / 2) (1 / 10) T →
        ∀ ρ : CMat (d ^ k), IsDensity ρ →
          quantumAlgorithmWith ρ σ A r R [d, k, N] [η]
            (B * ((k : ℝ) + N + inverseScale η) ^ C)
            (T + B * ((k : ℝ) + N + inverseScale η + logSize d) ^ C) (1 / 3)
            (fun s => ∃ b, outputsDecision s b ∧ sepDecision η ρ b) [P] returnsDecision := by sorry

end NuclearTensor.Membership.Supplement
