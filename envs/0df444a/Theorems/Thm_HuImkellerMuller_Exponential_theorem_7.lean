-- Prove2me | Theorems.Thm_HuImkellerMuller_Exponential_theorem_7
-- name    : HuImkellerMuller.Exponential.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:15.697447+00:00
-- url     : https://prove2.me/theorems/c79576f8-9c5f-42a0-b941-3b681623fc1e
-- title:
--   Theorem 7, p. 8 — V(x) = −exp(−α(x − Y₀)) for the unique bounded solution of the quadratic BSDE (7), and an optimal p* ∈ Π_{C_t}(Z_t + θ_t/α) exists
-- statement:
--   Let $W$ be an $m$-dimensional Brownian motion on $(\Omega,\mathcal F,P)$ and $\mathbb F$ the $P$-augmentation of its natural filtration, $T>0$. Consider a market of $d\le m$ stocks with predictable, uniformly bounded drift $b$ and volatility $\sigma$, $KI_d\ge\sigma\sigma^{\mathrm{tr}}\ge\varepsilon I_d$, and market price of risk $\theta_t=\sigma_t^{\mathrm{tr}}(\sigma_t\sigma_t^{\mathrm{tr}})^{-1}b_t$. Let $\tilde C\subseteq\mathbb R^{1\times d}$ be a closed, nonempty, not necessarily convex constraint set, $C_t=\tilde C\sigma_t$, let $\alpha>0$, and let the liability $F$ be $\mathcal F_T$-measurable and bounded. Let
--   $$V(x)=\sup_{p\in\mathcal A}E\Big[-\exp\Big(-\alpha\Big(x+\int_0^Tp_t\,(dW_t+\theta_t\,dt)-F\Big)\Big)\Big]\tag{5}$$
--   be the value function of exponential utility maximization over the admissible strategies $\mathcal A$. Then:
--
--   1. the BSDE
--   $$Y_t=F-\int_t^TZ_s\,dW_s-\int_t^Tf(s,Z_s)\,ds,\qquad f(\cdot,z)=-\frac\alpha2\operatorname{dist}^2\Big(z+\frac1\alpha\theta,C\Big)+z\theta+\frac1{2\alpha}|\theta|^2\tag{7}$$
--   has a solution $(Y,Z)\in\mathcal H^\infty(\mathbb R)\times\mathcal H^2(\mathbb R^m)$;
--   2. the solution is unique;
--   3. for every $x\in\mathbb R$,
--   $$V(x)=-\exp\big(-\alpha(x-Y_0)\big);$$
--   4. there is an optimal strategy $p^*\in\mathcal A$ with
--   $$p^*_t\in\Pi_{C_t(\omega)}\Big(Z_t+\frac1\alpha\theta_t\Big),\qquad t\in[0,T],\ P\text{-a.s.}\tag{8}$$
--
--   The theorem solves the exponential utility maximization problem with a bounded liability under closed, possibly nonconvex, constraints, by reducing it to a quadratic BSDE.
--
--   **Formalization Note** Parts 3 and 4 are stated for every solution $(Y,Z)$; with parts 1 and 2 this is "the unique solution". $Y_0$ is a.s. constant ($\mathcal F_0$ is trivial), so part 3 holds for $P$-a.e. $\omega$. Uniqueness is $Y^1_t=Y^2_t$ a.s. for each $t$ and $Z^1=Z^2$ $\lambda\otimes P$-a.e. The optimal $p^*$ is one predictable process, admissible and optimal for every initial capital $x$; (8) is read $\lambda\otimes P$-a.e. Expectations are minus lower integrals and $V$ is an extended real, so no non-integrable strategy is counted with the junk value 0. $\tilde C\neq\emptyset$ is added (otherwise $\mathcal A$ is empty). The filtration is the $P$-augmented Brownian filtration (the page: "completion"); the stochastic integral is the Itô-integral operator $I$.
-- source:
--   Hu, Imkeller, Müller (2005), arXiv:math/0508448v1, Theorem 7, pp. 8–9; problem (5), p. 7; Remark 5, p. 6

import Mathlib
import Definitions.Def_HuImkellerMuller_Exponential_BSDE

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace HuImkellerMuller.Exponential

/-- Theorem 7, pp. 8–9. -/
theorem theorem_7
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {d m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) (hT : 0 < T)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) (hW : EthierKurtz.IsStandardBrownian P W)
    (𝓕 : Filtration ℝ≥0 mΩ)
    (h𝓕 : CvitanicKaratzas92.Optimality.IsAugmentedBrownianFiltration P W 𝓕)
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m)) → ℝ≥0 → Ω → ℝ)
    (hI : CvitanicKaratzas92.Optimality.IsItoIntegralOperator P 𝓕 T W I)
    (b : ℝ≥0 → Ω → (Fin d → ℝ)) (σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin m) ℝ)
    (hmkt : MarketHyp P 𝓕 T b σ)
    (Ct : Set (Fin d → ℝ)) (hCt : IsClosed Ct) (hne : Ct.Nonempty)
    (α : ℝ) (hα : 0 < α)
    (F : Ω → ℝ) (hFmeas : Measurable[𝓕 T] F) (hFbdd : ∃ c : ℝ, ∀ᵐ ω ∂P, |F ω| ≤ c) :
    (∃ Y Z, IsSolution7 P 𝓕 T I b σ Ct α F Y Z) ∧
    (∀ Y₁ Z₁ Y₂ Z₂, IsSolution7 P 𝓕 T I b σ Ct α F Y₁ Z₁ →
        IsSolution7 P 𝓕 T I b σ Ct α F Y₂ Z₂ →
        (∀ t ≤ T, Y₁ t =ᵐ[P] Y₂ t) ∧
        ∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
          Z₁ q.1.toNNReal q.2 = Z₂ q.1.toNNReal q.2) ∧
    (∀ Y Z, IsSolution7 P 𝓕 T I b σ Ct α F Y Z → ∀ x : ℝ, ∀ᵐ ω ∂P,
        V P 𝓕 T I b σ Ct α F x = ((-Real.exp (-α * (x - Y 0 ω)) : ℝ) : EReal)) ∧
    (∀ Y Z, IsSolution7 P 𝓕 T I b σ Ct α F Y Z →
      ∃ pstar : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin m),
        IsPredictable 𝓕 pstar ∧
        (∀ᵐ q ∂(CvitanicKaratzas92.Optimality.lebP P T),
          pstar q.1.toNNReal q.2 ∈ proj (Cset Ct σ q.1.toNNReal q.2)
            (Z q.1.toNNReal q.2 + (1 / α) • theta b σ q.1.toNNReal q.2)) ∧
        ∀ x : ℝ, Admissible P 𝓕 T I b σ Ct α x pstar ∧
          expectedUtility P T I b σ α F x pstar = V P 𝓕 T I b σ Ct α F x) := by sorry

end HuImkellerMuller.Exponential
