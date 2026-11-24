-- Prove2me | Theorems.Thm_NeuralCollapseUFM_nuclear_norm_variational_form
-- name    : NeuralCollapseUFM.nuclear_norm_variational_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:15:39.038443+00:00
-- url     : https://prove2.me/theorems/3a73c565-4be7-405d-80f0-cb833ff985dd
-- title:
--   Lemma A.3: variational form of the nuclear norm
-- statement:
--   Let $Z\in\mathbb{R}^{K\times N}$, $\alpha>0$, and let $d\ge\operatorname{rank}Z$. Then
--
--   $$\|Z\|_*=\min_{\substack{W\in\mathbb{R}^{K\times d},\,H\in\mathbb{R}^{d\times N}\\ Z=WH}}\frac1{2\sqrt\alpha}\big(\|W\|_F^2+\alpha\|H\|_F^2\big).$$
--
--   That is, every factorization $Z=WH$ satisfies $\|Z\|_*\le\frac1{2\sqrt\alpha}(\|W\|_F^2+\alpha\|H\|_F^2)$, and some factorization attains equality.
--
--   This identity links the factored objective $f$ to the convex program (37) with the nuclear-norm penalty $\sqrt{\lambda_W\lambda_H}\|Z\|_*$.
--
--   **Formalization Note** The paper does not name the inner dimension $d$ of the factorization. The hypothesis $d\ge\operatorname{rank}Z$ makes the set of factorizations nonempty and the minimum attained. In Lemma C.2 and the proof of Theorem C.1 it is applied for arbitrary $d$, where only the inequality half is needed; that half holds for every $d$. The minimum is stated as a lower bound together with an attaining factorization.
-- source:
--   Zhu, Ding, Zhou, Li, You, Sulam and Qu, A Geometric Analysis of Neural Collapse with Unconstrained Features, arXiv:2105.02375v1 (2021), Appendix A, Lemma A.3, eq. (11), p. 28

import Mathlib
import Definitions.Def_NeuralCollapseUFM_Basic

open Matrix Filter Topology

namespace NeuralCollapseUFM

theorem nuclear_norm_variational_form {K N d : ℕ} (Z : Matrix (Fin K) (Fin N) ℝ) (α : ℝ)
    (hα : 0 < α) (hd : Z.rank ≤ d) :
    (∀ (W : Matrix (Fin K) (Fin d) ℝ) (H : Matrix (Fin d) (Fin N) ℝ), W * H = Z →
      nuclearNorm Z ≤ 1 / (2 * Real.sqrt α) * (frobSq W + α * frobSq H)) ∧
    ∃ (W : Matrix (Fin K) (Fin d) ℝ) (H : Matrix (Fin d) (Fin N) ℝ), W * H = Z ∧
      nuclearNorm Z = 1 / (2 * Real.sqrt α) * (frobSq W + α * frobSq H) := by sorry

end NeuralCollapseUFM
