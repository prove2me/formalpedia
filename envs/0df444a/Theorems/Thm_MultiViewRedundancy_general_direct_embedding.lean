-- Prove2me | Theorems.Thm_MultiViewRedundancy_general_direct_embedding
-- name    : MultiViewRedundancy.general_direct_embedding
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:21:09.865935+00:00
-- url     : https://prove2.me/theorems/279a0964-3b84-477f-b8c4-b136c82a94f6
-- title:
--   Lemma 7: low-dimensional direct embeddings from a hidden variable
-- statement:
--   Let $X$ and $Z$ take values in standard Borel spaces, and let $H\sim p_H$ render $X$ and $Z$ conditionally independent: $p_{X,Z}=\int p_{X\mid H}(\cdot\mid h)\otimes p_{Z\mid H}(\cdot\mid h)\,dp_H(h)$ with Markov kernels $p_{X\mid H}$, $p_{Z\mid H}$, where $p_{X\mid H}(\cdot\mid h)\ll p_X$ and $p_{Z\mid H}(\cdot\mid h)\ll p_Z$ for $p_H$-almost every $h$. For every integer $m>0$ there are measurable $\eta:\mathcal X\to\mathbb R^m$ and $\psi:\mathcal Z\to\mathbb R^m$ with
--
--   $$\mathbb E\big[(\eta(X)^\top\psi(\tilde Z)-g^\star(X,\tilde Z))^2\big]\le\frac1m\operatorname{var}\left(\frac{p_{X\mid H}(X\mid\bar H)\,p_{Z\mid H}(\tilde Z\mid\bar H)}{p_X(X)\,p_Z(\tilde Z)}\right),$$
--
--   where $(X,\tilde Z,\bar H)\sim p_X\otimes p_Z\otimes p_H$.
--
--   **Formalization Note** The ratios $p_{X\mid H}(x\mid h)/p_X(x)$ are Radon–Nikodym derivatives of the conditional laws with respect to the marginals. Their absolute continuity holds automatically when densities exist, as Section 2.1 assumes, and is a hypothesis here. Both sides take values in $[0,\infty]$. The paper's "there exist $\eta,\psi$" is read as measurable embeddings, as the expectation requires.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 4.2.1, Lemma 7, p. 11; proof in Appendix A.6, p. 19

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem general_direct_embedding {X Z H : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace H] [StandardBorelSpace X] [StandardBorelSpace Z]
    (ν : Measure (X × Z)) [IsProbabilityMeasure ν]
    (ρH : Measure H) [IsProbabilityMeasure ρH] (κX : Kernel H X) (κZ : Kernel H Z)
    [IsMarkovKernel κX] [IsMarkovKernel κZ] (hH : IsHiddenVariable ν ρH κX κZ)
    (hκX : ∀ᵐ h ∂ρH, κX h ≪ ν.fst) (hκZ : ∀ᵐ h ∂ρH, κZ h ≪ ν.snd)
    (m : ℕ) (hm : 0 < m) :
    ∃ (η : X → Fin m → ℝ) (ψ : Z → Fin m → ℝ), Measurable η ∧ Measurable ψ ∧
      epsDirect ν η ψ ≤ hiddenVar ν ρH κX κZ / m := by sorry

end MultiViewRedundancy
