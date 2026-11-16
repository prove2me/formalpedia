-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_lemma_7_4
-- name    : NuclearTensor.Membership.Supplement.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:50:31.730465+00:00
-- url     : https://prove2.me/theorems/08daeee7-db3b-4338-8608-23dd73fb931b
-- title:
--   Lemma 7.4 — discarded-mass estimation
-- statement:
--   For the local discarded masses $e_j=\operatorname{Tr}((I-F_j^2)A_j)$, every $\eta,\epsilon,p>0$ admits a routine returning classical estimates simultaneously satisfying
--
--   $$\Pr\{\forall j\in[k]:|\widehat e_j-e_j|\le\epsilon\}\ge1-p.$$
--
--   The routine uses $\operatorname{poly}(k,\eta^{-1},\epsilon^{-1},L(p))$ copies and this bound times a polynomial in $\ell(d)$ for total time. It estimates all parties rather than just a fixed one, supporting the rejection branch of Theorem 7.1.
--
--   **Formalization Note** The definitions of $A_j,F_j$ use the same cutoff as Lemma 7.3. The success event is simultaneous. There is no classical entry oracle for the unknown state.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: positive failure parameters and logarithmic confidence factors → all positive failure parameters, using L(x)=1+max(0,log(1/x)) in resource bounds; reason: agrees with logarithmic confidence scaling in the nontrivial range and accommodates the vacuous-success branch for x at least one
--   - reading: cutoff f_Theta(k^2/eta^4) → cutoff a=2048k^2/eta^4 from the proof on page 31; reason: fixes the source proof parameter without changing either promise or any resource dependence
--   - encoding: logarithmic dimension factors → ell(d)=1+ceil(log_2 d); reason: the usual positive input-size convention includes one-dimensional systems without a zero runtime bound
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 31, Lemma 7.4; supporting proof in pp. 48–49.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem lemma_7_4 :
    ∃ P : QProgram, ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k → ∀ η ε p : ℝ, 0 < η → 0 < ε → 0 < p →
      ∀ ρ : CMat (d ^ k), IsDensity ρ →
        quantumAlgorithm ρ σ A r P [d, k] [η, ε, p]
          (B * ((k : ℝ) + inverseScale η + inverseScale ε + confidence p) ^ C)
          (B * ((k : ℝ) + inverseScale η + inverseScale ε + confidence p) ^ C * (logSize d) ^ C)
          p (estimatesOutput ρ η ε) (returnsEstimates k) := by sorry

end NuclearTensor.Membership.Supplement
