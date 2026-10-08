-- Prove2me | Theorems.Thm_MultistageStochastic_distortion_avar_mixture
-- name    : MultistageStochastic.distortion_avar_mixture
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-23T20:23:41.001603+00:00
-- url     : https://prove2.me/theorems/033d90eb-87cd-40cb-8cc7-05365341049b
-- title:
--   (3.11) — a distortion risk functional is a mixture of Average Values-at-Risk
-- statement:
--   Let $\sigma$ be a distortion function. Then there is a probability measure $\mu$ on $[0,1]$,
--   depending on $\sigma$ only, such that on every probability space $(\Omega,\mathcal F,P)$ and
--   for every $Y\in L^\infty(P)$
--
--   $$
--   \mathcal R_\sigma(Y)\;=\;\int_0^1\mathsf{AV@R}_\alpha(Y)\,\mu(d\alpha) .
--   \tag{3.11}
--   $$
--
--   The source exhibits the measure: $\mu_\sigma(A)=\sigma(0)\,\delta_0(A)+\int_A(1-u)\,d\sigma(u)$,
--   (3.12), an atom at $0$ of mass $\sigma(0)$ plus the Lebesgue–Stieltjes measure of $\sigma$ weighted
--   by $1-u$, and verifies by integration by parts that it is a probability measure and that the
--   identity holds. This is the representation of "elementary importance" that identifies the
--   distortion functionals with the mixtures in Kusuoka's theorem (mission II) whose supremum
--   consists of a single measure.
--
--   **Formalization Note** The statement asserts the existence of the mixing measure rather than
--   constructing (3.12), because the Lebesgue–Stieltjes measure of a nondecreasing density is not
--   available in a form that makes the explicit formula shorter than the proof. The measure is
--   quantified **before** the probability space, as the source's $\mu_\sigma$ is built from
--   $\sigma$ alone: with the space bound first, $\mu$ could depend on $P$, and on a one-point space
--   every probability measure on $[0,1]$ would satisfy the identity. "Probability measure on $[0,1]$" is mission II's
--   `IsKusuokaMeasure`, and the Average Value-at-Risk at $\alpha=1$ is the essential supremum, as
--   there.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.2, printed p. 100 (PDF p. 113), representation (3.11): "R_σ(Y) = ∫_0^1 V@R_α(Y) σ(α) dα = ∫_0^1 AV@R_α(Y) μ_σ(dα) for a probability measure μ_σ on the interval [0, 1]", with μ_σ given by (3.12) and the identity established on printed p. 101 (PDF p. 114).

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic
theorem distortion_avar_mixture (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ) :
    ∃ μ : Measure ℝ, IsKusuokaMeasure μ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω), IsProbabilityMeasure P →
        ∀ Y, MemLinfty P Y →
          distortionFunctional P σ Y = ∫ α, averageValueAtRisk P Y α ∂μ := by sorry
end MultistageStochastic
