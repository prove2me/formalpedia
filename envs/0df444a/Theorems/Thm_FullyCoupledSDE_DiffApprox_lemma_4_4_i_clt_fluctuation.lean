-- Prove2me | Theorems.Thm_FullyCoupledSDE_DiffApprox_lemma_4_4_i_clt_fluctuation
-- name    : FullyCoupledSDE.DiffApprox.lemma_4_4_i_clt_fluctuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:25.471316+00:00
-- url     : https://prove2.me/theorems/0b65b5a8-b8bb-4f6d-be5d-e28e8c946e48
-- title:
--   Lemma 4.4(i), p. 1226 — CLT-type fluctuation estimate in Regime 1: E((1/γ)∫_0^t f ds) ≤ C_t(α^ϑ/γ + α²/γ² + α²/(βγ))
-- statement:
--   Assume (Aσ), (Ab), (2.7) and $\delta\in(0,1]$, and place ourselves in Regime 1: $\alpha_\varepsilon,\beta_\varepsilon,\gamma_\varepsilon>0$ tend to $0$, $\alpha_\varepsilon^2/\beta_\varepsilon\to0$, $\alpha_\varepsilon/\gamma_\varepsilon\to0$ and $\alpha_\varepsilon^2/(\beta_\varepsilon\gamma_\varepsilon)\to0$. Let $b,\sigma\in C^{\delta,\vartheta}_b$ with $\vartheta\in(0,2]$, $c,F,H,G\in L^\infty_p$, and let $f\in C^{\vartheta/2,\delta,\vartheta}_p$ satisfy the centering condition (1.3) with respect to the invariant measures $\mu^y$ of (1.7). Fix $t>0$ and $(x,y)$. Then there are $C_t>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ and every weak solution $(X^\varepsilon,Y^\varepsilon)$ of (1.4) on $[0,t]$ started at $(x,y)$, the path integral below exists a.s., is integrable, and
--   $$\mathbb E\Big(\frac1{\gamma_\varepsilon}\int_0^tf(s,X^\varepsilon_s,Y^\varepsilon_s)\,ds\Big)\le C_t\Big(\frac{\alpha_\varepsilon^\vartheta}{\gamma_\varepsilon}+\frac{\alpha_\varepsilon^2}{\gamma_\varepsilon^2}+\frac{\alpha_\varepsilon^2}{\beta_\varepsilon\gamma_\varepsilon}\Big).$$
--
--   This controls the fluctuation term $\gamma_\varepsilon^{-1}\int_0^tH(s,X^\varepsilon_s,Y^\varepsilon_s)\,ds$ of the slow equation, which in Regime 1 vanishes in the limit; it is the second ingredient of the rate in Theorem 2.3(i).
--
--   **Formalization Note.** The two Regime 1 limits are hypotheses, following the label "(Regime 1)" of part (i); the page derives (i) from Lemma 4.2 by $\alpha^{1+(\vartheta\wedge1)}_\varepsilon/\gamma^2_\varepsilon\le C(\alpha_\varepsilon^\vartheta/\gamma_\varepsilon+\alpha_\varepsilon^2/\gamma_\varepsilon^2)$, which needs $\alpha_\varepsilon/\gamma_\varepsilon$ bounded when $\vartheta<1$. The bound is one-sided, as printed; integrability is part of the conclusion. (2.7) is read with $\alpha_\varepsilon^2/\beta_\varepsilon$ in place of $\varepsilon$.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1226, Lemma 4.4(i); proof of (i), p. 1229

import Mathlib
import Definitions.Def_FullyCoupledSDE_DiffApprox_Setting

namespace FullyCoupledSDE.DiffApprox

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Lemma 4.4(i), p. 1226 (Regime 1). Fluctuation estimate of CLT type: for a centered
`f ∈ C^{ϑ/2,δ,ϑ}_p`, `E (1/γ) ∫_0^t f(s, X^ε_s, Y^ε_s) ds ≤ C_t (α^ϑ/γ + α²/γ² + α²/(βγ))`,
for every weak solution of (1.4) started at `(x, y)` and every small `ε`. -/
theorem lemma_4_4_i_clt_fluctuation {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (F H : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2) (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (δ ϑ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2) (α β γ : ℝ → ℝ)
    (hσ : AssumpSigma σ) (hb : FullyCoupledSDE.Poisson.AssumpB b) (h27 : Assump27 b c) (hμ : IsInvariantFamily σ b μ)
    (hb_reg : Cb δ ϑ b) (hσ_reg : Cb δ ϑ (fun x y => Matrix.of.symm (σ x y)))
    (hc : LpInf (fun (_ : ℝ≥0) => c)) (hF : LpInf F) (hH : LpInf H)
    (hG : LpInf (fun t x y => Matrix.of.symm (G t x y)))
    (hpar : StandingParams α β γ) (hreg1 : Regime1 α β γ)
    (f : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → ℝ) (hf : CpT (ϑ / 2) δ ϑ f) (hf_c : CenteredT μ f)
    (t : ℝ≥0) (ht : 0 < t) (x : FullyCoupledSDE.Poisson.E d1) (y : FullyCoupledSDE.Poisson.E d2) :
    ∃ C > (0 : ℝ), ∃ ε0 > (0 : ℝ), ∀ ε ∈ Set.Ioo (0 : ℝ) ε0,
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω)
        [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → Fin (d1 + d2) → ℝ)
        (Z : ℝ≥0 → Ω → Fin d1 ⊕ Fin d2 → ℝ),
      IsSolution14 σ b c F H G (α ε) (β ε) (γ ε) t x y 𝓕 P W Z →
        (∀ᵐ ω ∂P, IntegrableOn
            (fun s : ℝ => f s.toNNReal (xOf (Z s.toNNReal ω)) (yOf (Z s.toNNReal ω)))
            (Set.Icc 0 (t : ℝ))) ∧
        Integrable (fun ω => ∫ s in Set.Icc (0 : ℝ) t,
            f s.toNNReal (xOf (Z s.toNNReal ω)) (yOf (Z s.toNNReal ω))) P ∧
        ∫ ω, (1 / γ ε) * (∫ s in Set.Icc (0 : ℝ) t,
            f s.toNNReal (xOf (Z s.toNNReal ω)) (yOf (Z s.toNNReal ω))) ∂P ≤
          C * (α ε ^ ϑ / γ ε + α ε ^ 2 / γ ε ^ 2 + α ε ^ 2 / (β ε * γ ε)) := by sorry

end FullyCoupledSDE.DiffApprox
