-- Prove2me | Theorems.Thm_GaussianBCSecondOrder_moments_normal_approximation
-- name    : GaussianBCSecondOrder.moments_normal_approximation
-- status  : Open
-- author  : @Vincent Tan
-- created : 2026-11-23T07:28:35.232295+00:00
-- url     : https://prove2.me/theorems/779b55b3-31f6-457e-a90f-5cb460bbd96d
-- title:
--   Lemma 4: moments and normal approximation of the information densities
-- statement:
--   This lemma computes the first two moments of the information densities of eq. (49) and gives Berry-Esseen-type normal approximations for them.
--
--   Let $S_1>S_2>0$, and let $\iota_0,\iota_1,\iota_2$ be the information densities of eq. (49) for deterministic $u^n,v^n$ satisfying eq. (48), as random variables in the noise $(Z_1^n,Z_2^n)$. Let $C_0(\alpha)=\mathsf C(S_1)-\mathsf C(\alpha S_1)$ and $V_0(\alpha)=\mathsf V(S_1)+\mathsf V(\alpha S_1)-2\mathsf V(\alpha S_1,S_1)$.
--
--   **Lemma.** Fix $n\ge3$, $\alpha\in(0,1)$, $\rho\in[-1,1]$ and $u^n,v^n$ satisfying eq. (48).
--
--   1. For $j=0,1,2$: $\ \mathbb E[\iota_j]=nC_j(\alpha)$ and $\mathrm{Var}(\iota_j)=nV_j(\alpha)$; moreover $\mathrm{Cov}(\iota_1,\iota_2)=nV_{12}(\alpha,\rho)$.
--   2. There is a constant $B<\infty$ depending only on $S_1,S_2$ such that for $j=0,1,2$,
--   $$\sup_{t\in\mathbb R}\Big|\Pr(\iota_j\le t)-\Phi\Big(\frac{t-nC_j(\alpha)}{\sqrt{nV_j(\alpha)}}\Big)\Big|\le\frac B{\sqrt n},$$
--   uniformly over $\alpha\in(0,1)$, $\rho\in[-1,1]$ and all pairs $(u^n,v^n)$.
--   3. For every compact interval $I\subset(0,1)$ there is a constant $B_I<\infty$ depending only on $I,S_1,S_2$ such that for all $\alpha\in I$,
--   $$\sup_{t_1,t_2\in\mathbb R}\Big|\Pr(\iota_1>t_1,\iota_2>t_2)-\Psi_{\alpha,\rho}\Big(\frac{nC_1(\alpha)-t_1}{\sqrt n},\frac{nC_2(\alpha)-t_2}{\sqrt n}\Big)\Big|\le\frac{B_I}{\sqrt n},$$
--   uniformly over $\rho\in[-1,1]$ and all pairs $(u^n,v^n)$.
--
--   The lemma identifies $V_1,V_2,V_{12}$ as the per-letter variances and covariance of the information densities, which is where the dispersion matrix $\Sigma_\alpha(\rho)$ comes from.
--
--   **Formalization Note** The standing assumption $S_1>S_2>0$ is a hypothesis. Uniformity is expressed by the order of quantifiers: $B$ is chosen before $n,\alpha,\rho,u^n,v^n,t$, and $B_I$ before $n,\alpha\in I,\rho,u^n,v^n,t_1,t_2$. A compact interval $I\subset(0,1)$ is $[a,b]$ with $0<a\le b<1$. Suprema over $t$ are stated as bounds for every $t$.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, p. 11, Lemma 4, eqs. (55)-(58), with eqs. (48), (49), (54)

import Definitions.Def_GaussianBCSecondOrder_Superposition

open MeasureTheory ProbabilityTheory Filter Topology

namespace GaussianBCSecondOrder
theorem moments_normal_approximation (S₁ S₂ : ℝ) (hS₂ : 0 < S₂) (hS : S₂ < S₁) :
    (∀ n : ℕ, 3 ≤ n → ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u v : EuclideanSpace ℝ (Fin n), IsSuperpositionPair α u v →
        (∫ z, info₀ S₁ α u v z ∂(noiseLaw S₁ S₂ ρ n) = n * C₀ S₁ α ∧
          variance (info₀ S₁ α u v) (noiseLaw S₁ S₂ ρ n) = n * V₀ S₁ α) ∧
        (∫ z, info₁ S₁ α u v z ∂(noiseLaw S₁ S₂ ρ n) = n * C₁ S₁ α ∧
          variance (info₁ S₁ α u v) (noiseLaw S₁ S₂ ρ n) = n * V₁ S₁ α) ∧
        (∫ z, info₂ S₂ α u v z ∂(noiseLaw S₁ S₂ ρ n) = n * C₂ S₂ α ∧
          variance (info₂ S₂ α u v) (noiseLaw S₁ S₂ ρ n) = n * V₂ S₂ α) ∧
        covariance (info₁ S₁ α u v) (info₂ S₂ α u v) (noiseLaw S₁ S₂ ρ n) =
          n * V₁₂ S₁ S₂ α ρ) ∧
    (∃ B : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
      ∀ u v : EuclideanSpace ℝ (Fin n), IsSuperpositionPair α u v → ∀ t : ℝ,
        |(noiseLaw S₁ S₂ ρ n).real {z | info₀ S₁ α u v z ≤ t} -
            Phi ((t - n * C₀ S₁ α) / Real.sqrt (n * V₀ S₁ α))| ≤ B / Real.sqrt n ∧
        |(noiseLaw S₁ S₂ ρ n).real {z | info₁ S₁ α u v z ≤ t} -
            Phi ((t - n * C₁ S₁ α) / Real.sqrt (n * V₁ S₁ α))| ≤ B / Real.sqrt n ∧
        |(noiseLaw S₁ S₂ ρ n).real {z | info₂ S₂ α u v z ≤ t} -
            Phi ((t - n * C₂ S₂ α) / Real.sqrt (n * V₂ S₂ α))| ≤ B / Real.sqrt n) ∧
    (∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      ∃ B : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ α ∈ Set.Icc a b, ∀ ρ ∈ Set.Icc (-1 : ℝ) 1,
        ∀ u v : EuclideanSpace ℝ (Fin n), IsSuperpositionPair α u v → ∀ t₁ t₂ : ℝ,
          |(noiseLaw S₁ S₂ ρ n).real {z | t₁ < info₁ S₁ α u v z ∧ t₂ < info₂ S₂ α u v z} -
              Psi S₁ S₂ α ρ ((n * C₁ S₁ α - t₁) / Real.sqrt n)
                ((n * C₂ S₂ α - t₂) / Real.sqrt n)| ≤ B / Real.sqrt n) := by sorry
end GaussianBCSecondOrder
