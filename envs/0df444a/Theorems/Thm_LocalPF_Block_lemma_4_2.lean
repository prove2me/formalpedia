-- Prove2me | Theorems.Thm_LocalPF_Block_lemma_4_2
-- name    : LocalPF.Block.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:32.647979+00:00
-- url     : https://prove2.me/theorems/daab163c-8e57-4ffb-9917-f94f0bbdbc53
-- title:
--   Lemma 4.2, p. 32 — reweighting by Λ with a ≤ Λ ≤ b multiplies ‖·‖ and |||·||| by at most 2b/a
-- statement:
--   Let $\mu,\nu$ be probability measures on a measurable space, and let $\Lambda$ be a measurable function with $0<a\le\Lambda(x)\le b$ for all $x$. Define the reweighted probability measures
--   $$\mu_\Lambda(A)=\frac{\int 1_A(x)\Lambda(x)\,\mu(dx)}{\int\Lambda(x)\,\mu(dx)},\qquad \nu_\Lambda(A)=\frac{\int 1_A(x)\Lambda(x)\,\nu(dx)}{\int\Lambda(x)\,\nu(dx)}.$$
--   Then
--   $$\|\mu_\Lambda-\nu_\Lambda\|\le 2\,\frac{b}{a}\,\|\mu-\nu\|.$$
--
--   With $a=\inf_x\Lambda(x)$ and $b=\sup_x\Lambda(x)$ this is the paper's bound $2\frac{\sup\Lambda}{\inf\Lambda}\|\mu-\nu\|$. The same conclusion holds for the norm $|||\rho-\rho'|||=\sup_{|f|\le1}\mathbf E[|\rho(f)-\rho'(f)|^2]^{1/2}$ of random probability measures: if $\omega\mapsto\mu_\omega,\nu_\omega$ are random probability measures on a probability space $(\Omega,\mathbf P)$ and $|||\mu-\nu|||\le B$, then
--   $$|||\mu_\Lambda-\nu_\Lambda|||\le 2\,\frac{b}{a}\,B.$$
--   The lemma controls the correction step $\mathsf C$ of the filter, which is a reweighting by the observation likelihood.
--
--   **Formalization Note** The paper's "bounded and strictly positive" is read as $\inf\Lambda>0$, which is what makes its right-hand side finite; the bounds $a,b$ are explicit hypotheses, and the statement with the best $a,b$ is the paper's. The lemma's two sentences are the two conjuncts. In the second, a random probability measure is a Giry-measurable map $\Omega\to\mathcal P(\mathbb S)$ (what "random measure" presupposes), and $|||\rho-\rho'|||\le B$ is written as $\mathbf E[(\rho(f)-\rho'(f))^2]\le B^2$ for every measurable $f$ with $|f|\le1$ (equivalent for $B\ge0$), the expectation being a lower Lebesgue integral.
-- source:
--   Rebeschini & van Handel, Can Local Particle Filters Beat the Curse of Dimensionality?, arXiv:1301.6585v2 (reprint of Ann. Appl. Probab. 25(5), 2015), p. 32, Lemma 4.2

import Mathlib
import Definitions.Def_LocalPF_Block_Setting

open MeasureTheory
open scoped ENNReal

namespace LocalPF.Block

/-- Lemma 4.2 (pp. 32–33), with `a ≤ inf Λ` and `b ≥ sup Λ`: the `‖·‖` form for probability
measures `μ`, `ν`, and the `|||·|||` form for random probability measures `ω ↦ μr ω`, `ω ↦ νr ω`
on a probability space `(Ω, P)`, where `|||μr − νr||| ≤ B` is stated as
`E[(μr(f) − νr(f))²] ≤ B²` for every measurable `f` with `|f| ≤ 1`. -/
theorem lemma_4_2 {S : Type*} [MeasurableSpace S] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (Λ : S → ℝ) (hΛ : Measurable Λ)
    (a b : ℝ) (ha : 0 < a) (hab : ∀ x, a ≤ Λ x ∧ Λ x ≤ b) :
    tv (reweight Λ μ) (reweight Λ ν) ≤ ENNReal.ofReal (2 * (b / a)) * tv μ ν ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (μr νr : Ω → Measure S), Measurable μr → Measurable νr →
      (∀ ω, IsProbabilityMeasure (μr ω)) → (∀ ω, IsProbabilityMeasure (νr ω)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ f : S → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
        ∫⁻ ω, ENNReal.ofReal ((∫ x, f x ∂(μr ω) - ∫ x, f x ∂(νr ω)) ^ 2) ∂P ≤
          ENNReal.ofReal (B ^ 2)) →
      ∀ f : S → ℝ, Measurable f → (∀ x, |f x| ≤ 1) →
        ∫⁻ ω, ENNReal.ofReal ((∫ x, f x ∂(reweight Λ (μr ω)) -
            ∫ x, f x ∂(reweight Λ (νr ω))) ^ 2) ∂P ≤
          ENNReal.ofReal ((2 * (b / a) * B) ^ 2) := by sorry

end LocalPF.Block
