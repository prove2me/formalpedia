-- Prove2me | Theorems.Thm_NoisyMC_Convex_claim_3
-- name    : NoisyMC.Convex.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:42.177982+00:00
-- url     : https://prove2.me/theorems/a156dc71-343d-4e57-a431-cd56e9c7226c
-- title:
--   Claim 3 — the Q of an approximate critical point: ‖Σ_Q − Σ_Q^{-1}‖_F ≤ 8√κ p‖∇f‖_F/(λ√σ_min) ≤ 8c√(c_inj p/κ)
-- statement:
--   Work under the notation and assumptions of Lemma 2. Thus $M=M^\star+E$, where $M^\star$ has rank $r\ge1$ with extreme singular values $\sigma_{\max},\sigma_{\min}$ and condition number $\kappa$; $0<p\le1$, $\lambda>0$, $c_{\rm inj}>0$; the factors $X,Y\in\mathbb R^{n\times r}$ have all singular values in $[\sqrt{\sigma_{\min}/2},\sqrt{2\sigma_{\max}}]$, satisfy Conditions 1 and 2 (with $c_{\rm inj}$), and
--
--   $$\|\nabla f(X,Y)\|_F\le c\,\frac{\sqrt{c_{\rm inj}p}}{\kappa}\cdot\frac\lambda p\sqrt{\sigma_{\min}}\qquad(23)$$
--
--   for a constant $c>0$. Let $U\Sigma V^\top$ be an SVD of $XY^\top$. Then there is an invertible $Q\in\mathbb R^{r\times r}$ with $X=U\Sigma^{1/2}Q$, $Y=V\Sigma^{1/2}Q^{-\top}$ and, with $U_Q\Sigma_QV_Q^\top$ the SVD of $Q$,
--
--   $$\|\Sigma_Q-\Sigma_Q^{-1}\|_F\le8\sqrt\kappa\,\frac{p}{\lambda\sqrt{\sigma_{\min}}}\,\|\nabla f(X,Y)\|_F\le8c\sqrt{c_{\rm inj}p/\kappa}.\qquad(62)$$
--
--   At an approximate critical point of the regularized nonconvex objective the two factors are therefore nearly balanced. This is the step of the proof of Claim 2 that bounds the tangent component of the residual.
--
--   **Formalization Note.** $\|\Sigma_Q-\Sigma_Q^{-1}\|_F$ is stated as $\|Q-(Q^{-1})^\top\|_F$, which is equal (see Lemma 20). The statement holds for every $c>0$: the first inequality does not involve $c$, and the second is (23) rearranged. The constants 8 are those of the paper. $\sigma_{\max},\sigma_{\min},\kappa$ refer to $M^\star$, not to $XY^\top$.
-- source:
--   Chen, Chi, Fan, Ma, Yan, Noisy Matrix Completion: Understanding Statistical Guarantees for Convex Relaxation via Nonconvex Optimization, authors' preprint (Sep. 2019; arXiv:1902.07698), p. 28, Claim 3, (62)

import Mathlib
import Definitions.Def_NoisyMC_Convex_Setup

open MatrixCompletion MeasureTheory ProbabilityTheory

namespace NoisyMC.Convex

/-- Claim 3 (p. 28). Under the notation and assumptions of Lemma 2 (with any constant `c > 0` in
(23)), let `U Σ Vᵀ` be an SVD of `X Yᵀ`. There is an invertible `Q ∈ ℝ^{r×r}` with
`X = U Σ^{1/2} Q`, `Y = V Σ^{1/2} Q^{-ᵀ}` and (62):
`‖Σ_Q − Σ_Q^{-1}‖_F ≤ 8√κ · p/(λ√σ_min) · ‖∇f(X,Y)‖_F ≤ 8c √(c_inj p/κ)`,
where `‖Σ_Q − Σ_Q^{-1}‖_F = ‖Q − Q^{-ᵀ}‖_F`. Here `M = M⋆ + E`, and `σ_max, σ_min, κ` are those
of `M⋆`. -/
theorem claim_3 (c : ℝ) (hc : 0 < c) {n r : ℕ} (hr : 1 ≤ r)
    (Mstar Emat : RealMatrix n n) (S : SVD Mstar r) (Ω : Finset (Fin n × Fin n))
    (p lam cinj : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hlam : 0 < lam) (hcinj : 0 < cinj)
    (X Y : RealMatrix n r)
    (hX : SingularValuesIn X (sigmaMin S / 2) (2 * sigmaMax S))
    (hY : SingularValuesIn Y (sigmaMin S / 2) (2 * sigmaMax S))
    (hC1 : Condition1 Ω Mstar Emat p lam X Y) (hC2 : Condition2 Ω p cinj X Y)
    (hgrad : gradNorm Ω (Mstar + Emat) lam p X Y ≤
      c * (Real.sqrt (cinj * p) / condNum S) * (lam / p) * Real.sqrt (sigmaMin S))
    (SX : SVD (X * Y.transpose) r) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ,
      IsUnit Q.det ∧
      X = svdU SX * svdSigmaSqrt SX * Q ∧
      Y = svdV SX * svdSigmaSqrt SX * (Q⁻¹).transpose ∧
      frobeniusNorm (Q - (Q⁻¹).transpose) ≤
        8 * Real.sqrt (condNum S) * (p / (lam * Real.sqrt (sigmaMin S))) *
          gradNorm Ω (Mstar + Emat) lam p X Y ∧
      8 * Real.sqrt (condNum S) * (p / (lam * Real.sqrt (sigmaMin S))) *
          gradNorm Ω (Mstar + Emat) lam p X Y ≤
        8 * c * Real.sqrt (cinj * p / condNum S) := by sorry

end NoisyMC.Convex
