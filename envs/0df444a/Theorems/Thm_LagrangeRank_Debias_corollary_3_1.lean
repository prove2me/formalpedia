-- Prove2me | Theorems.Thm_LagrangeRank_Debias_corollary_3_1
-- name    : LagrangeRank.Debias.corollary_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:28.491626+00:00
-- url     : https://prove2.me/theorems/45e82cbe-4511-4818-b162-502dc04fa572
-- title:
--   Corollary 3.1, p. 17 — ‖Θ̂ − Θ*‖∞ ≲ r₁ + r₄ (blocks (B.1)–(B.3))
-- statement:
--   Let $c_1,c_2,L_2\in\mathbb R$ and $c_3>0$. There are constants $C,\delta>0$, depending only on $c_1,c_2,c_3,L_2$ and **not on the dimension**, such that the following holds for every $d$.
--
--   Let $\widehat\Omega,\Omega^*\in\mathbb R^{d\times d}$ and $\widehat g,g^*\in\mathbb R^d$, and let $\rho_1,\rho_4\ge0$ with $\rho_1+\rho_4\le\delta$. Suppose
--   $$\|g^*\|_1\le c_1,\quad \|\widehat g-g^*\|_1\le L_2\rho_1,\quad \|\Omega^*\|_\infty\le c_2,\quad g^{*\top}\Omega^*g^*\ge c_3,\quad \|\widehat\Omega-\Omega^*\|_\infty\le\rho_4 .$$
--   Then, with $\widehat\Theta=\Theta(\widehat\Omega,\widehat g)$ and $\Theta^*=\Theta(\Omega^*,g^*)$ the block-inverse matrices of p. 16,
--   $$|\widehat\Theta_{22}-\Theta^*_{22}|\le C(\rho_1+\rho_4),\qquad \|\widehat\Theta_{12}-\Theta^*_{12}\|_\infty\le C(\rho_1+\rho_4),\qquad \|\widehat\Theta_{11}-\Theta^*_{11}\|_\infty\le C(\rho_1+\rho_4).$$
--
--   In the paper, $\widehat g=\nabla f(\widehat\theta)$, $g^*=\nabla f(\theta^*)$, $\rho_1\asymp r_1$ and $\rho_4\asymp r_4$, so this is Corollary 3.1, $\|\widehat\Theta-\Theta^*\|_\infty\lesssim r_1+r_4$, on the three blocks (B.1)–(B.3) that its proof bounds. These are the blocks the proofs of Lemma A.1 and Theorem 3.1 use.
--
--   **Formalization Note.** The $\lesssim$ is made quantitative: $C$ and $\delta$ are chosen after $c_1,c_2,c_3,L_2$ and before $d$. The smallness $\rho_1+\rho_4\le\delta$ is the paper's "recall $r_1,r_4=o(1)$" (p. 43). The hypothesis $\|\widehat g-g^*\|_1\le L_2\rho_1$ is Assumption 3.3 at $t=1$ combined with Assumption 3.1. The printed claim is the $\infty$-norm of the whole $(d+1)\times(d+1)$ difference; its last row contains $\|\widehat\Theta_{12}-\Theta^*_{12}\|_1$, which needs column sums of $\widehat\Omega$ that Assumption 3.4 does not control, and the proof (B.1)–(B.3) bounds only the three blocks stated here.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 17, Corollary 3.1; proof in Appendix B.1, pp. 43–44, (B.1)–(B.3)

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix
theorem corollary_3_1 (c1 c2 c3 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ)
        (ρ1 ρ4 : ℝ),
        0 ≤ ρ1 → 0 ≤ ρ4 → ρ1 + ρ4 ≤ δ →
        l1Norm gStar ≤ c1 → l1Norm (gHat - gStar) ≤ L2 * ρ1 →
        rowSumNorm OmStar ≤ c2 → c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        |(thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₂₂ () ()|
            ≤ C * (ρ1 + ρ4) ∧
        ‖fun k => (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₂ k ()‖
            ≤ C * (ρ1 + ρ4) ∧
        rowSumNorm (thetaBlock OmHat gHat - thetaBlock OmStar gStar).toBlocks₁₁
            ≤ C * (ρ1 + ρ4) := by sorry
end LagrangeRank.Debias
