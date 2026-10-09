-- Prove2me | Theorems.Thm_GaussianMatrix_herbst_argument
-- name    : GaussianMatrix.herbst_argument
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T04:25:05.053986+00:00
-- url     : https://prove2.me/theorems/b2180479-3891-40fc-a8a7-fb271da903de
-- title:
--   Herbst's argument: an entropy bound $\mathrm{Ent}(e^{sf})\le c s^2\,\mathbb{E}e^{sf}$ for all $s>0$ implies $\mathbb{E}e^{sf}\le e^{s\mathbb{E}f+cs^2}$
-- statement:
--   Let $(\Omega, \mu)$ be a probability space, $c \in \mathbb{R}$, and $f : \Omega \to \mathbb{R}$ a function such that $e^{sf}$ is $\mu$-integrable for every $s \in \mathbb{R}$. Write $M(s) = \int e^{sf}\,d\mu$ and
--   $$\mathrm{Ent}_\mu(e^{sf}) = \int s f\, e^{sf}\, d\mu - M(s)\log M(s)$$
--   for the entropy of $e^{sf}$. Suppose that
--   $$\mathrm{Ent}_\mu(e^{sf}) \le c\, s^2\, M(s) \qquad \text{for every } s > 0 .$$
--   Then for every $s \ge 0$,
--   $$\int e^{sf}\, d\mu \;\le\; \exp\Big(s \int f\, d\mu + c\, s^2\Big).$$
--
--   This is Herbst's argument, which turns a logarithmic Sobolev type inequality into a sub-Gaussian bound on the moment generating function. With $c = L^2/2$ and the Gaussian entropy bound for $L$-Lipschitz functions, it gives $\mathbb{E}\,e^{s(f - \mathbb{E}f)} \le e^{s^2L^2/2}$; the Chernoff bound then yields sharp Gaussian concentration.
--
--   **Formalization Note.** The integrability hypothesis for all real $s$ implies that $f$ itself is integrable, so $\int f\,d\mu$ is the true mean. No sign condition on $c$ is assumed. Entropy is nonnegative and $M(s) > 0$, so the hypothesis already forces $c \ge 0$.
-- source:
--   S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities (Oxford Univ. Press, 2013), Proposition 6.1 (Herbst's argument), stated there with $v = 2c$; M. Ledoux, The Concentration of Measure Phenomenon (AMS, 2001), §5.1, Theorem 5.3. Numbering is cited from memory.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem herbst_argument {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (c : ℝ) (hint : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * f ω)) μ)
    (hent : ∀ s : ℝ, 0 < s →
      ∫ ω, s * f ω * Real.exp (s * f ω) ∂μ
        - (∫ ω, Real.exp (s * f ω) ∂μ) * Real.log (∫ ω, Real.exp (s * f ω) ∂μ)
        ≤ c * s ^ 2 * ∫ ω, Real.exp (s * f ω) ∂μ)
    (s : ℝ) (hs : 0 ≤ s) :
    ∫ ω, Real.exp (s * f ω) ∂μ ≤ Real.exp (s * ∫ ω, f ω ∂μ + c * s ^ 2) := by sorry

end GaussianMatrix
