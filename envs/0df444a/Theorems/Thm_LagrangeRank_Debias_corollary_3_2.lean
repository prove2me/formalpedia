-- Prove2me | Theorems.Thm_LagrangeRank_Debias_corollary_3_2
-- name    : LagrangeRank.Debias.corollary_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:24.796167+00:00
-- url     : https://prove2.me/theorems/db7b9b8c-7d4b-4237-93cb-9365c6c0a505
-- title:
--   Corollary 3.2, p. 17 — ‖I − Θ̂Σ̂‖∞ ≲ r₃ (blocks 11, 12, 22)
-- statement:
--   Let $c_1,c_2,L_2\in\mathbb R$ and $c_3>0$. There are constants $C,\delta>0$, depending only on $c_1,c_2,c_3,L_2$ and not on the dimension, such that for every $d$ the following holds.
--
--   Let $\widehat\Omega,\Omega^*,H\in\mathbb R^{d\times d}$, $\widehat g,g^*\in\mathbb R^d$ and $\rho_1,\rho_3,\rho_4\ge0$ with $\rho_1+\rho_4\le\delta$, and assume
--   $$\|g^*\|_1\le c_1,\ \ \|\widehat g-g^*\|_1\le L_2\rho_1,\ \ \|\Omega^*\|_\infty\le c_2,\ \ g^{*\top}\Omega^*g^*\ge c_3,\ \ \|\widehat\Omega-\Omega^*\|_\infty\le\rho_4,\ \ \|I-\widehat\Omega H\|_\infty\le\rho_3 .$$
--   Let $\widehat\Theta=\Theta(\widehat\Omega,\widehat g)$ be the block-inverse estimator of p. 16 and $\widehat\Sigma=\begin{pmatrix}H&\widehat g\\ \widehat g^\top&0\end{pmatrix}$ the bordered Hessian (3.6). Then
--   $$\|(I-\widehat\Theta\widehat\Sigma)_{11}\|_\infty\le C\rho_3,\qquad (I-\widehat\Theta\widehat\Sigma)_{12}=0,\qquad (I-\widehat\Theta\widehat\Sigma)_{22}=0 .$$
--
--   With $H=\nabla^2L(\widehat\theta)$ and $\rho_3\asymp r_3$ this is Corollary 3.2, $\|I-\widehat\Theta\widehat\Sigma\|_\infty\lesssim r_3$, on the blocks its proof (B.2) treats and that the proof of Lemma A.1 uses.
--
--   **Formalization Note.** Constants are chosen before $d$. The lower-left block $\widehat g^\top(\widehat\Omega^\top H-I)/(\widehat g^\top\widehat\Omega\widehat g)$ is omitted: the proof in B.2 bounds it through $\|(\widehat\Omega\nabla^2L(\widehat\theta))^\top-I\|_\infty$, which Assumption 3.4 does not provide, and the goal never uses it. The two zero blocks require $\widehat g^\top\widehat\Omega\widehat g\neq0$, which follows from $\rho_1+\rho_4\le\delta$.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 17, Corollary 3.2; proof in Appendix B.2, pp. 44–45

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

namespace LagrangeRank.Debias
open Matrix
theorem corollary_3_2 (c1 c2 c3 L2 : ℝ) (hc3 : 0 < c3) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (d : ℕ) (OmHat OmStar H : Matrix (Fin d) (Fin d) ℝ) (gHat gStar : Fin d → ℝ)
        (ρ1 ρ3 ρ4 : ℝ),
        0 ≤ ρ1 → 0 ≤ ρ3 → 0 ≤ ρ4 → ρ1 + ρ4 ≤ δ →
        l1Norm gStar ≤ c1 → l1Norm (gHat - gStar) ≤ L2 * ρ1 →
        rowSumNorm OmStar ≤ c2 → c3 ≤ gStar ⬝ᵥ (OmStar *ᵥ gStar) →
        rowSumNorm (OmHat - OmStar) ≤ ρ4 →
        rowSumNorm (1 - OmHat * H) ≤ ρ3 →
        rowSumNorm (1 - thetaBlock OmHat gHat * borderedHessian H gHat).toBlocks₁₁
            ≤ C * ρ3 ∧
        (1 - thetaBlock OmHat gHat * borderedHessian H gHat).toBlocks₁₂ = 0 ∧
        (1 - thetaBlock OmHat gHat * borderedHessian H gHat).toBlocks₂₂ = 0 := by sorry
end LagrangeRank.Debias
