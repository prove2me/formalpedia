-- Prove2me | Theorems.Thm_FullyCoupledSDE_DiffApprox_lemma_4_2_lln_fluctuation
-- name    : FullyCoupledSDE.DiffApprox.lemma_4_2_lln_fluctuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:45.300978+00:00
-- url     : https://prove2.me/theorems/e2b733de-a56b-4144-a160-f6c04cba68d1
-- title:
--   Lemma 4.2, p. 1223 — LLN-type fluctuation estimate E∫_0^t f(s,X^ε_s,Y^ε_s)ds ≤ C_t(α^ϑ + α^{ϑ∧1}·α/γ + α²/β) for centered f
-- statement:
--   Assume (Aσ), (Ab) and (2.7). Let $0<\delta\le1$, $0<\vartheta\le2$, $b,\sigma\in C^{\delta,\vartheta}_b$ and $c,F,H,G\in L^\infty_p$, and let $\alpha_\varepsilon,\beta_\varepsilon,\gamma_\varepsilon>0$ tend to $0$ with $\alpha_\varepsilon^2/\beta_\varepsilon\to0$. Let $\mu^y$ be the invariant measures of the frozen equation (1.7), $f\in C^{\vartheta/2,\delta,\vartheta}_p$ centered, $\int f(t,x,y)\mu^y(dx)=0$, and fix $t>0$ and $(x,y)$. Then there are $C_t>0$ and $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ and every weak solution $(X^\varepsilon,Y^\varepsilon)$ of (1.4) on $[0,t]$ started at $(x,y)$, the path integral of $s\mapsto f(s,X^\varepsilon_s,Y^\varepsilon_s)$ over $[0,t]$ exists a.s., is integrable, and
--   $$\mathbb E\Big(\int_0^tf(s,X^\varepsilon_s,Y^\varepsilon_s)\,ds\Big)\le C_t\Big(\alpha_\varepsilon^\vartheta+\alpha_\varepsilon^{\vartheta\wedge1}\cdot\frac{\alpha_\varepsilon}{\gamma_\varepsilon}+\frac{\alpha_\varepsilon^2}{\beta_\varepsilon}\Big).$$
--
--   $C_t$ depends on the data but not on $\varepsilon$. This is a quantitative law of large numbers: the time average of a centered function along the fast motion is small. Applied to $-f$ it gives the two-sided bound used in the proof of Theorem 2.3.
--
--   **Formalization Note.** The page prints "$0<\delta,\vartheta\le2$"; $\delta$ is taken in $(0,1]$, the range in which the classes are defined. The bound is one-sided, as printed. The integrability of the path integral and of its expectation is part of the conclusion, so the bound cannot hold through a junk value. (2.7) is read with the factor $\alpha_\varepsilon^2/\beta_\varepsilon$ that multiplies $c$ in the fast drift in place of $\varepsilon$. Solutions are weak: any filtered probability space, any Brownian motion for its filtration.
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1223, Lemma 4.2

import Mathlib
import Definitions.Def_FullyCoupledSDE_DiffApprox_Setting

namespace FullyCoupledSDE.DiffApprox

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Lemma 4.2, p. 1223. Fluctuation estimate of LLN type: for a centered
`f ∈ C^{ϑ/2,δ,ϑ}_p`, `E ∫_0^t f(s, X^ε_s, Y^ε_s) ds ≤ C_t (α^ϑ + α^{ϑ∧1}·α/γ + α²/β)`,
for every weak solution of (1.4) started at `(x, y)` and every small `ε`. -/
theorem lemma_4_2_lln_fluctuation {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (F H : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2) (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (δ ϑ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2) (α β γ : ℝ → ℝ)
    (hσ : AssumpSigma σ) (hb : FullyCoupledSDE.Poisson.AssumpB b) (h27 : Assump27 b c) (hμ : IsInvariantFamily σ b μ)
    (hb_reg : Cb δ ϑ b) (hσ_reg : Cb δ ϑ (fun x y => Matrix.of.symm (σ x y)))
    (hc : LpInf (fun (_ : ℝ≥0) => c)) (hF : LpInf F) (hH : LpInf H)
    (hG : LpInf (fun t x y => Matrix.of.symm (G t x y)))
    (hpar : StandingParams α β γ)
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
        ∫ ω, (∫ s in Set.Icc (0 : ℝ) t,
            f s.toNNReal (xOf (Z s.toNNReal ω)) (yOf (Z s.toNNReal ω))) ∂P ≤
          C * (α ε ^ ϑ + α ε ^ min ϑ 1 * (α ε / γ ε) + α ε ^ 2 / β ε) := by sorry

end FullyCoupledSDE.DiffApprox
