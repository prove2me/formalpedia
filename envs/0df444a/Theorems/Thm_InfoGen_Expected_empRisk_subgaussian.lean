-- Prove2me | Theorems.Thm_InfoGen_Expected_empRisk_subgaussian
-- name    : InfoGen.Expected.empRisk_subgaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:39.613455+00:00
-- url     : https://prove2.me/theorems/dec7a784-508d-4ffc-83b4-92da9202a6ad
-- title:
--   §3.2, p. 4 — if ℓ(w,Z) is σ-subgaussian for every w, then each empirical risk L_S(w) is σ/√n-subgaussian under μ^{⊗n}
-- statement:
--   Let $\mathsf Z$ be an instance space, $\mathsf W$ a hypothesis space, $\ell:\mathsf W\times\mathsf Z\to\mathbb R_+$ a nonnegative, jointly measurable loss, and $\mu$ a probability measure on $\mathsf Z$. Let $n\ge 1$ and let $S=(Z_1,\dots,Z_n)\sim\mu^{\otimes n}$ be an i.i.d. sample. Write $L_\mu(w)=\mathbb E[\ell(w,Z)]$ for the population risk and $L_S(w)=\frac1n\sum_{i=1}^n\ell(w,Z_i)$ for the empirical risk.
--
--   Suppose that for every $w\in\mathsf W$ the random variable $\ell(w,Z)$, $Z\sim\mu$, is $\sigma$-subgaussian: $\log\mathbb E[e^{\lambda(\ell(w,Z)-L_\mu(w))}]\le\lambda^2\sigma^2/2$ for all $\lambda\in\mathbb R$. Then for every $w\in\mathsf W$ the empirical risk $L_S(w)$ is $\sigma/\sqrt n$-subgaussian under $\mu^{\otimes n}$:
--   $$
--   \log\mathbb E\Big[e^{\lambda\,(L_S(w)-L_\mu(w))}\Big]\le\frac{\lambda^2\sigma^2}{2n}\qquad\text{for all }\lambda\in\mathbb R .
--   $$
--
--   This is the first half of the step that connects Lemma 1 to the learning problem: with $f(s,w)=L_s(w)$, each section $f(S,w)$ inherits subgaussianity from the loss, with the variance proxy reduced by the factor $n$ because of the i.i.d. sample.
--
--   **Formalization Note** Subgaussianity is Mathlib's `HasSubgaussianMGF` of the centred variable, whose parameter is the variance proxy: $\sigma^2$ for the loss, $\sigma^2/n$ for the empirical risk. Joint measurability of $\ell$ and $n\ge1$ are added (the page assumes both implicitly). The page's nonnegativity of $\ell$ is kept as a hypothesis although it plays no role.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, §3.2, p. 4, first sentence ("f(S, w) is σ/√n-subgaussian due to the i.i.d. assumption on Z_i's"), with f(s, w) defined on p. 3

import Mathlib
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.Expected

open LearnStability.Characterization

/-- §3.2, p. 4, first clause (Xu & Raginsky, arXiv:1705.07809v2). If `ℓ(w, Z)` is
`σ`-subgaussian under `μ` for every hypothesis `w`, then for every `w` the empirical risk
`L_S(w) = f(S, w)` of an i.i.d. sample `S ∼ μ^{⊗n}` is `σ/√n`-subgaussian: its centred version
`L_S(w) − L_μ(w)` has variance proxy `σ²/n`. -/
theorem empRisk_subgaussian {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ) :
    ∀ w, HasSubgaussianMGF (fun s => empRisk ℓ s w - risk ℓ μ w) (σ ^ 2 / n)
      (sampleLaw μ n) := by sorry

end InfoGen.Expected
