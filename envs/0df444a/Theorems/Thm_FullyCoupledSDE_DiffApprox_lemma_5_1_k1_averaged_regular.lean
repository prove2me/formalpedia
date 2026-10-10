-- Prove2me | Theorems.Thm_FullyCoupledSDE_DiffApprox_lemma_5_1_k1_averaged_regular
-- name    : FullyCoupledSDE.DiffApprox.lemma_5_1_k1_averaged_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:45.906834+00:00
-- url     : https://prove2.me/theorems/406020ae-db1e-41a2-bd50-c11029963e78
-- title:
--   Lemma 5.1 (k = 1), p. 1230 — 𝒢̂_1 is nondegenerate in y uniformly in t, and F̂_1, 𝒢̂_1 ∈ C^{ϑ/2,ϑ}_b
-- statement:
--   Assume the hypotheses of Theorem 2.3(i): (Aσ), (Ab), (AG), (AH) and (2.7); $\delta\in(0,1]$, $\vartheta\in(0,2]$; $b,\sigma\in C^{\delta,\vartheta}_b$, $F,H,G\in C^{\vartheta/2,\delta,\vartheta}_p$ and $c\in L^\infty_p$; and let $\mu^y$ be the invariant measures of the frozen equation (1.7). Let
--   $$\hat F_1(t,y)=\int_{\mathbb R^{d_1}}F(t,x,y)\,\mu^y(dx),\qquad \hat{\mathcal G}_1(t,y)=\frac12\int_{\mathbb R^{d_1}}GG^*(t,x,y)\,\mu^y(dx)=\frac12\hat G_1\hat G_1^*(t,y).$$
--   Then
--
--   1. $\hat{\mathcal G}_1$ is nondegenerate in $y$ uniformly with respect to $t$: there is $\lambda>1$ with $\lambda^{-1}|\xi|^2\le|\hat{\mathcal G}_1(t,y)\xi|^2\le\lambda|\xi|^2$ for all $t,y,\xi$;
--   2. $\hat F_1,\hat{\mathcal G}_1\in C^{\vartheta/2,\vartheta}_b$: bounded, $\vartheta/2$-Hölder in time and of class $C^\vartheta_b$ in $y$, uniformly.
--
--   These are the properties of the averaged coefficients that make the limit equation (2.9) well posed and its Kolmogorov equation regular enough for the proof of Theorem 2.3.
--
--   **Formalization Note.** Only the case $k=1$ of the lemma (stated for $k=1,\dots,4$) is posed. Nondegeneracy is read in the form of (AG). The classes are those of the definitions file (constants uniform in $t$; $t=0$ included).
-- source:
--   Röckner & Xie, Diffusion approximation for fully coupled SDEs, Ann. Probab. 49 (2021), p. 1230, Lemma 5.1 (case k = 1); 𝒢̂_k defined p. 1229

import Mathlib
import Definitions.Def_FullyCoupledSDE_DiffApprox_Setting

namespace FullyCoupledSDE.DiffApprox

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- Lemma 5.1, p. 1230, case `k = 1`, under the assumptions of Theorem 2.3(i): `𝒢̂_1` is
nondegenerate in `y` uniformly in `t`, and `F̂_1, 𝒢̂_1 ∈ C^{ϑ/2,ϑ}_b`. -/
theorem lemma_5_1_k1_averaged_regular {d1 d2 : ℕ} (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (σ : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d1) (Fin d1) ℝ) (b c : FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d1)
    (F H : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → FullyCoupledSDE.Poisson.E d2) (G : ℝ≥0 → FullyCoupledSDE.Poisson.E d1 → FullyCoupledSDE.Poisson.E d2 → Matrix (Fin d2) (Fin d2) ℝ)
    (μ : FullyCoupledSDE.Poisson.E d2 → Measure (FullyCoupledSDE.Poisson.E d1)) (δ ϑ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hϑ : ϑ ∈ Set.Ioc (0 : ℝ) 2)
    (hσ : AssumpSigma σ) (hb : FullyCoupledSDE.Poisson.AssumpB b) (hG : AssumpG G) (hH : CenteredT μ H)
    (h27 : Assump27 b c) (hμ : IsInvariantFamily σ b μ)
    (hb_reg : Cb δ ϑ b) (hσ_reg : Cb δ ϑ (fun x y => Matrix.of.symm (σ x y)))
    (hF_reg : CpT (ϑ / 2) δ ϑ F) (hH_reg : CpT (ϑ / 2) δ ϑ H)
    (hG_reg : CpT (ϑ / 2) δ ϑ (fun t x y => Matrix.of.symm (G t x y)))
    (hc : LpInf (fun (_ : ℝ≥0) => c)) :
    (∃ lam > (1 : ℝ), ∀ (t : ℝ≥0) (y : FullyCoupledSDE.Poisson.E d2) (ξ : FullyCoupledSDE.Poisson.E d2),
      lam⁻¹ * ‖ξ‖ ^ 2 ≤ ‖Matrix.toEuclideanLin (GcalHat1 μ G t y) ξ‖ ^ 2 ∧
      ‖Matrix.toEuclideanLin (GcalHat1 μ G t y) ξ‖ ^ 2 ≤ lam * ‖ξ‖ ^ 2) ∧
    CbTY (ϑ / 2) ϑ (Fhat1 μ F) ∧
    CbTY (ϑ / 2) ϑ (fun t y => Matrix.of.symm (GcalHat1 μ G t y)) := by sorry

end FullyCoupledSDE.DiffApprox
