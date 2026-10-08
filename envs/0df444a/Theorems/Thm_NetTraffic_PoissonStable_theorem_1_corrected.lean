-- Prove2me | Theorems.Thm_NetTraffic_PoissonStable_theorem_1_corrected
-- name    : NetTraffic.PoissonStable.theorem_1_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:41.282513+00:00
-- url     : https://prove2.me/theorems/6ff10afe-7c70-4808-9f7e-5ded686637cc
-- title:
--   Theorem 1 (corrected), p. 33 — under slow growth, (A(T·) − Tλμ_on(·))/b(λT) →fidi X_{α,C_α^{−1/α},1}
-- statement:
--   Throughout, $F_{\mathrm{on}}$ is a probability law on $[0,\infty)$ satisfying (2.8): $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $1<\alpha<2$ and $L$ slowly varying; $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$; $b=(1/\bar F_{\mathrm{on}})^{\leftarrow}$ is the quantile function (2.9); the connection rate $\lambda=\lambda(T)>0$ is a non-decreasing function of $T$ (§3.1), and $b(\lambda T)$ means $b$ evaluated at $\lambda(T)\,T$. Each $T$ carries its own probability space $(\Omega_T,P_T)$ with an infinite source Poisson model of rate $\lambda(T)$ and length law $F_{\mathrm{on}}$; the statement holds for every such family. Let $C_\alpha=(1-\alpha)/(\Gamma(2-\alpha)\cos(\pi\alpha/2))$ and let $X_{\alpha,\sigma,\beta}$ denote α-stable Lévy motion: independent stationary increments, $X(0)=0$, $X(t)-X(s)\sim S_\alpha(\sigma(t-s)^{1/\alpha},\beta,0)$.
--
--   **Theorem.** If Slow Growth Condition 1 holds, then
--   $$\frac{A(T\cdot)-T\lambda\mu_{\mathrm{on}}(\cdot)}{b(\lambda T)}\xrightarrow{\ fidi\ }X_{\alpha,C_\alpha^{-1/\alpha},1}(\cdot).$$
--   Explicitly: for every $k$ and all $0\le t_1\le\dots\le t_k$ there is a probability law $\nu$ on $\mathbb R^k$ whose characteristic function is
--   $$\theta\mapsto\prod_{j=1}^k\exp\Big\{-C_\alpha^{-1}(t_j-t_{j-1})\,|u_j|^\alpha\big(1-i\,\mathrm{sign}(u_j)\tan(\pi\alpha/2)\big)\Big\},\qquad u_j=\theta_j+\dots+\theta_k,\ t_0=0,$$
--   (the law of $(X_{\alpha,C_\alpha^{-1/\alpha},1}(t_1),\dots,X_{\alpha,C_\alpha^{-1/\alpha},1}(t_k))$), and the law of
--   $$\Big(\frac{A(Tt_j)-T\lambda\mu_{\mathrm{on}}t_j}{b(\lambda T)}\Big)_{j=1}^k$$
--   converges weakly to $\nu$ as $T\to\infty$.
--
--   Under slow growth of the connection rate, the cumulative input of the infinite source Poisson model is asymptotically a totally skewed α-stable Lévy motion: a process with independent increments, as opposed to the fractional Brownian motion obtained under fast growth.
--
--   **Correction.** The paper prints the limit $X_{\alpha,1,1}$ (scale $1$). Its own proof gives the tail limit $\lambda T\,P(j_1>b(\lambda T)x)\to x^{-\alpha}$ (pp. 37–38), which identifies the Lévy measure $\alpha x^{-\alpha-1}dx$; the stable law with that Lévy measure has scale $\sigma=C_\alpha^{-1/\alpha}$ (Samorodnitsky–Taqqu, Property 1.2.15, and the paper's own criterion on p. 47 with $c=1$), the same $\sigma$ the paper prints in Theorem 2. Since $C_\alpha\in(0,2/\pi)$ for $\alpha\in(1,2)$, the printed scale is wrong; this statement carries the corrected scale.
--
--   **Formalization Note** Times are taken sorted and non-negative (any finite set of times can be sorted). The limit is given by its characteristic function on $\mathbb R^k$ (as `EuclideanSpace`), and its existence is part of the claim. Convergence of the finite-dimensional distributions is weak convergence of the laws of the vectors, each a.e. measurable.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 33, Theorem 1 (limit scale corrected, see description)

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology

theorem theorem_1_corrected
    {Fon : Measure ℝ} [IsProbabilityMeasure Fon] {α : ℝ} (hF : HeavyTail Fon α)
    {lam : ℝ → ℝ} (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (hC1 : Condition1 Fon lam)
    {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, IsPoissonModel (P T) (lam T) Fon (Γ T) (X T)) :
    ∀ (k : ℕ) (t : Fin k → ℝ), Monotone t → (∀ j, 0 ≤ t j) →
      ∃ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
        (∀ θ : EuclideanSpace ℝ (Fin k), charFun (ν : Measure (EuclideanSpace ℝ (Fin k))) θ =
          stableLevyFidiCharFun α (sigmaConst α) 1 t θ) ∧
        TendstoInLaw P (fun T ω =>
          (WithLp.toLp 2 (fun j => Gnorm Fon lam (Γ T) (X T) T (t j) ω) :
            EuclideanSpace ℝ (Fin k))) ν := by sorry

end NetTraffic.PoissonStable
