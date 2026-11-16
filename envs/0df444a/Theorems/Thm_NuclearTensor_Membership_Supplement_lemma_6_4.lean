-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_lemma_6_4
-- name    : NuclearTensor.Membership.Supplement.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:45:08.785297+00:00
-- url     : https://prove2.me/theorems/0f5083b0-16e6-4c91-8872-687ad9550dd3
-- title:
--   Lemma 6.4 — LocalSearch with value estimates
-- statement:
--   Let $\omega$ be an unknown state on $(\mathbb C^q)^{\otimes m}$, and let $K=\sum_{\ell=1}^T c_\ell\bigotimes_jK_{\ell,j}$ be explicit, with real $c_\ell$, Hermitian factors satisfying $\|K_{\ell,j}\|_F\le1$, and $G=1+\sum_\ell|c_\ell|$. A unit product reference $a$ has $m-1$ factors. Define
--
--   $$R(a,\alpha)=\{x=\bigotimes_jx_j:\|x_j\|=1,\ |\langle a,x_{[m-1]}\rangle|^2\ge\alpha\}.$$
--
--   For every $\alpha,\epsilon,\delta>0$, a quantum algorithm returns a unit product $\widehat x$ and real $v$. With probability at least $1-\delta$, both clauses hold: if the regional maximum is at least $\epsilon$, then its value at $\widehat x$ is within $\epsilon$ of that maximum, and
--
--   $$|v-\operatorname{Tr}((\omega-K)|\widehat x\rangle\langle\widehat x|)|\le\epsilon.$$
--
--   Copy complexity has exponent $O(\log(G/(\alpha\epsilon)))$ and a logarithmic confidence factor; total time is $\operatorname{poly}_{\alpha,\epsilon,G}(m,q,T,L(\delta))$. This supplies the full LocalSearch contract used by the cover and signed optimizer.
--
--   **Formalization Note** The proof's truncation uses $h=4e\log(32G/(\alpha\epsilon))$. The all-positive-parameter reading uses internal $\bar\alpha=\min(\alpha,1)$ and $\bar\epsilon=\min(\epsilon,1)$ and copy bound $b(1+mq)^{c\log(32G/(\bar\alpha\bar\epsilon))}L(\delta)$, with absolute positive $b,c$. External accuracies are unchanged. For $\alpha>1$ only the regional optimization clause is vacuous; the value clause remains required.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: positive failure parameters and logarithmic confidence factors → all positive failure parameters, using L(x)=1+max(0,log(1/x)) in resource bounds; reason: agrees with logarithmic confidence scaling in the nontrivial range and accommodates the vacuous-success branch for x at least one
--   - reading: the printed exponent O(log(G/(alpha epsilon))) with all positive parameters → copy exponent c log(32G/(min(alpha,1) min(epsilon,1))); reason: uses Algorithm 3 and Appendix A truncation scale and clamps only internal tolerances; the two external-accuracy clauses remain intact
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 23, Lemma 6.4; supporting proof in pp. 40–43.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem lemma_6_4 :
    ∃ b c : ℕ, 0 < b ∧ 0 < c ∧
      ∀ α ε G : ℝ, 0 < α → 0 < ε → 1 ≤ G → ∃ P : QProgram,
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d m T : ℕ, 0 < d → 0 < m → ∀ δ : ℝ, 0 < δ →
      ∀ K : SignedOperator d m T, K.G = G →
      ∀ a : Fin (m - 1) → CVec d, (∀ j, normSq (a j) = 1) →
      ∀ ω : CMat (d ^ m), IsDensity ω →
        quantumAlgorithm ω σ A r P [d, m, T]
          ([α, ε, δ] ++ encodeSigned K ++ encodeProducts a)
          (b * Real.rpow (1 + (m : ℝ) * d)
            (c * Real.log (32 * G / (min α 1 * min ε 1))) * confidence δ)
          (B * (1 + m + d + T + confidence δ) ^ C) δ
          (localSearchOutput ω K a α ε) (returnsProductValue d m) := by sorry

end NuclearTensor.Membership.Supplement
