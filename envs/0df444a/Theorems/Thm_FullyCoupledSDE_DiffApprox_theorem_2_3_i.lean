-- Prove2me | Theorems.Thm_FullyCoupledSDE_DiffApprox_theorem_2_3_i
-- name    : FullyCoupledSDE.DiffApprox.theorem_2_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:57.447386+00:00
-- url     : https://prove2.me/theorems/10617644-885d-461a-957a-828ae6954402
-- title:
--   Theorem 2.3(i), p. 1212 — Regime 1: sup_{t≤T}|Eφ(Y^ε_t) − Eφ(Ŷ^1_t)| ≤ C_T(α^ϑ/γ + α²/γ² + α²/(βγ))
-- statement:
--   Consider the fully coupled two-scale system (1.4),
--   $$dX^\varepsilon_t=\alpha_\varepsilon^{-2}b(X^\varepsilon_t,Y^\varepsilon_t)dt+\beta_\varepsilon^{-1}c(X^\varepsilon_t,Y^\varepsilon_t)dt+\alpha_\varepsilon^{-1}\sigma(X^\varepsilon_t,Y^\varepsilon_t)dW^1_t,$$
--   $$dY^\varepsilon_t=F(t,X^\varepsilon_t,Y^\varepsilon_t)dt+\gamma_\varepsilon^{-1}H(t,X^\varepsilon_t,Y^\varepsilon_t)dt+G(t,X^\varepsilon_t,Y^\varepsilon_t)dW^2_t,$$
--   $X^\varepsilon_0=x\in\mathbb R^{d_1}$, $Y^\varepsilon_0=y\in\mathbb R^{d_2}$, where $\alpha_\varepsilon,\beta_\varepsilon,\gamma_\varepsilon>0$ tend to $0$ with $\alpha_\varepsilon^2/\beta_\varepsilon\to0$. Let $\mu^y$ be the invariant measure of the frozen equation $dX^y_t=b(X^y_t,y)dt+\sigma(X^y_t,y)dW^1_t$.
--
--   Assume (Aσ), (Ab), (AG), (AH) (the drift $H$ is centered: $\int H(t,x,y)\mu^y(dx)=0$) and (2.7); let $T>0$, $\delta\in(0,1]$ and $\vartheta\in(0,2]$. Suppose we are in Regime 1, $\alpha_\varepsilon/\gamma_\varepsilon\to0$ and $\alpha_\varepsilon^2/(\beta_\varepsilon\gamma_\varepsilon)\to0$, that $b,\sigma\in C^{\delta,\vartheta}_b$, $F,H,G\in C^{\vartheta/2,\delta,\vartheta}_p$, $c\in L^\infty_p$, and further that $\alpha_\varepsilon^\vartheta/\gamma_\varepsilon\to0$. Let $\hat Y^1$ solve the averaged equation (2.9),
--   $$d\hat Y^1_t=\hat F_1(t,\hat Y^1_t)dt+\hat G_1(t,\hat Y^1_t)dW^2_t,\quad\hat Y^1_0=y,\qquad \hat F_1=\int F\,d\mu^y,\ \ \hat G_1\hat G_1^*=\int GG^*\,d\mu^y.$$
--   Then for every $\varphi\in C^{2+\vartheta}_b(\mathbb R^{d_2})$ there are $C_T>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every weak solution of (1.4) and every weak solution of (2.9) on $[0,T]$,
--   $$\sup_{t\in[0,T]}\big|\mathbb E[\varphi(Y^\varepsilon_t)]-\mathbb E[\varphi(\hat Y^1_t)]\big|\le C_T\Big(\frac{\alpha_\varepsilon^\vartheta}{\gamma_\varepsilon}+\frac{\alpha_\varepsilon^2}{\gamma_\varepsilon^2}+\frac{\alpha_\varepsilon^2}{\beta_\varepsilon\gamma_\varepsilon}\Big).$$
--
--   The slow component thus converges weakly to the classical averaged diffusion, with a rate that depends only on the regularity of the coefficients in the slow variable.
--
--   **Formalization Note.** $C_T$ comes after all the data ($b,c,\sigma,F,H,G,\mu,\hat G,T,\delta,\vartheta,\alpha,\beta,\gamma,\varphi,x,y$) and before $\varepsilon$; "independent of $\delta$" adds nothing once the data are fixed. The supremum is a bound for every $t\le T$ with one constant. $\hat G_1$ is any measurable matrix field with $\hat G_1\hat G_1^*=\int GG^*d\mu^y$ (the law of $\hat Y^1$ depends only on $\hat G_1\hat G_1^*$), which covers the printed square root. The statement is about all weak solutions of (1.4) and (2.9) on arbitrary filtered probability spaces; the paper does not prove existence for (1.4). $\mu^y$ is the infinitesimally invariant family for $\mathscr L_0$ with $a=\sigma\sigma^*/2$. (2.7) is read with $\alpha_\varepsilon^2/\beta_\varepsilon$ in place of $\varepsilon$.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1212, Theorem 2.3(i); proof pp. 1230–1231

import Mathlib
import Definitions.Def_FullyCoupledSDE_DiffApprox_Setting

namespace FullyCoupledSDE.DiffApprox

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Theorem 2.3(i), p. 1212 (Regime 1). Weak convergence of the slow component `Y^ε` of (1.4) to
the averaged SDE (2.9) with `F̂_1`, `Ĝ_1`, at the rate
`sup_{t ≤ T} |𝔼 φ(Y^ε_t) − 𝔼 φ(Ŷ^1_t)| ≤ C_T (α^ϑ/γ + α²/γ² + α²/(βγ))`, for every weak solution
of (1.4) started at `(x, y)`, every weak solution of (2.9) started at `y`, and every small `ε`. -/
theorem theorem_2_3_i {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (F H : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2) (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (Ghat : ℝ≥0 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (T : ℝ≥0) (hT : 0 < T) (δ ϑ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2) (α β γ : ℝ → ℝ)
    (hσ : AssumpSigma σ) (hb : FullyCoupledSDE.Poisson.AssumpB b) (hG : AssumpG G) (hH : CenteredT μ H)
    (h27 : Assump27 b c) (hμ : IsInvariantFamily σ b μ)
    (hb_reg : Cb δ ϑ b) (hσ_reg : Cb δ ϑ (fun x y => Matrix.of.symm (σ x y)))
    (hF_reg : CpT (ϑ / 2) δ ϑ F) (hH_reg : CpT (ϑ / 2) δ ϑ H)
    (hG_reg : CpT (ϑ / 2) δ ϑ (fun t x y => Matrix.of.symm (G t x y)))
    (hc : LpInf (fun (_ : ℝ≥0) => c))
    (hpar : StandingParams α β γ) (hreg1 : Regime1 α β γ)
    (hrate : Tendsto (fun ε => α ε ^ ϑ / γ ε) (𝓝[>] 0) (𝓝 0))
    (hGhat : IsGhat1 μ G Ghat)
    (φ : FullyCoupledSDE.Poisson.E d2 → ℝ) (hφ : CbY (2 + ϑ) φ) (x : FullyCoupledSDE.Poisson.E d1) (y : FullyCoupledSDE.Poisson.E d2) :
    ∃ C > (0 : ℝ), ∃ ε0 > (0 : ℝ), ∀ ε ∈ Set.Ioo (0 : ℝ) ε0,
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
        [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → Fin (d1 + d2) → ℝ)
        (Z : ℝ≥0 → Ω → Fin d1 ⊕ Fin d2 → ℝ),
      IsSolution14 σ b c F H G (α ε) (β ε) (γ ε) T x y 𝓕 P W Z →
      ∀ (Ω' : Type) [mΩ' : MeasurableSpace Ω'] (𝓕' : Filtration ℝ≥0 mΩ') (P' : Measure Ω')
        [IsProbabilityMeasure P'] (W' : ℝ≥0 → Ω' → Fin d2 → ℝ) (Yh : ℝ≥0 → Ω' → Fin d2 → ℝ),
      IsSolution29 (Fhat1 μ F) Ghat T y 𝓕' P' W' Yh →
      ∀ t ≤ T,
        |∫ ω, φ (yOf (Z t ω)) ∂P - ∫ ω, φ (WithLp.toLp 2 (Yh t ω)) ∂P'| ≤
          C * (α ε ^ ϑ / γ ε + α ε ^ 2 / γ ε ^ 2 + α ε ^ 2 / (β ε * γ ε)) := by sorry

end FullyCoupledSDE.DiffApprox
