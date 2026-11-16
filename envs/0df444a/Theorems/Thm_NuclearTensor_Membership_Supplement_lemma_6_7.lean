-- Prove2me | Theorems.Thm_NuclearTensor_Membership_Supplement_lemma_6_7
-- name    : NuclearTensor.Membership.Supplement.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:46:41.021941+00:00
-- url     : https://prove2.me/theorems/075d197d-4a73-4ee7-b8e1-c2b76b75a51c
-- title:
--   Lemma 6.7 — product-overlap covers
-- statement:
--   For every $\theta>0$ and unknown state $\rho$ on $(\mathbb C^d)^{\otimes k}$, a quantum algorithm returns a finite list of unit products $C$. With probability at least $1-100k\delta/\theta^2$, it is a $\theta$-overlap cover:
--
--   $$\operatorname{Tr}(\rho|x\rangle\langle x|)\ge\theta\quad\Longrightarrow\quad\exists c\in C:\ |\langle x,c\rangle|\ge\theta^2/64.$$
--
--   Time and copies are $O_\theta(\operatorname{poly}(kd)L(\delta))$, with constants independent of $d,k,\rho,\delta$. This is the cover support for Theorem 6.1.
--
--   **Formalization Note** The proof's cap yields at most $(\lceil8/\theta\rceil+1)^2\le100/\theta^2$ LocalSearch calls per layer for $0<\theta\le1$, giving the displayed explicit failure bound. For $\theta>1$ coverage is vacuous and the empty cover is valid. The overlap bound concerns amplitude.
--
--   Differences from the source:
--   - encoding: finite complex Hilbert spaces and Hilbert–Schmidt geometry → row-major complex matrices on Fin (d^k), explicit pure-product hull, and an extended-nonnegative Frobenius-distance infimum; reason: these coordinates cover every finite-dimensional source instance; no density or norm restriction is added to the classical Hermitian input
--   - reading: algorithms with classical arithmetic and quantum copy access → finite arithmetic/spectral programs and elementary H,T,CX programs with Born-rule execution, charged fresh copies, and explicit classical outputs; reason: makes the computational model and all resource claims operational; neither global optimization nor a desired quantum subroutine is a primitive
--   - encoding: O and polynomial resource notation → positive integer multiplicative constants and degrees quantified before varying instance parameters; reason: preserves the indicated parameter dependencies and ties each bound to actual executed charges
--   - encoding: positive failure parameters and logarithmic confidence factors → all positive failure parameters, using L(x)=1+max(0,log(1/x)) in resource bounds; reason: agrees with logarithmic confidence scaling in the nontrivial range and accommodates the vacuous-success branch for x at least one
--   - encoding: failure O(k delta/theta^2) → failure at most 100k delta/theta^2; reason: the literal loop cap bounds calls per layer by (ceil(8/theta)+1)^2 at most 100/theta^2 for theta at most one; larger theta has vacuous coverage
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p. 25, Lemma 6.7; supporting proof in pp. 43–45.

import Definitions.Def_NuclearTensor_Membership_Supplement_Tasks

set_option autoImplicit false
noncomputable section

namespace NuclearTensor.Membership.Supplement

theorem lemma_6_7 :
    ∀ θ : ℝ, 0 < θ → ∃ P : QProgram,
      ∀ (σ : Spectral) (A r : ℕ), 0 < A → 0 < r →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ d k : ℕ, 0 < d → 0 < k → ∀ δ : ℝ, 0 < δ →
      ∀ ρ : CMat (d ^ k), IsDensity ρ →
        quantumAlgorithm ρ σ A r P [d, k] [θ, δ]
          (B * (1 + (k : ℝ) * d) ^ C * confidence δ)
          (B * (1 + (k : ℝ) * d) ^ C * confidence δ)
          (100 * k * δ / θ ^ 2) (coverOutput ρ θ) (returnsCover d k) := by sorry

end NuclearTensor.Membership.Supplement
