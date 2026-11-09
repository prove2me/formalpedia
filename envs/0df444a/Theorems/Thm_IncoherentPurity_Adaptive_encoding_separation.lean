-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_encoding_separation
-- name    : IncoherentPurity.Adaptive.encoding_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:26.312471+00:00
-- url     : https://prove2.me/theorems/e57b7d50-54b4-4ae4-9e4c-a1e00600b474
-- title:
--   Lemma 6.4 — Purity concentration and separation
-- statement:
--   With the sufficiently small absolute $c_0$ and the joint large-dimension, small-precision choices of Section 6, put $p_i=1/d+Dv_i$ and
--
--   $$V_i=\{\theta:|\operatorname{tr}(\rho_\theta^2)-p_i|\le\varepsilon/d\}.$$
--
--   For both unconditioned Gaussian priors, $\Pr(\theta\notin V_i)\le .01$. In addition, every pair $\theta_0\in V_0,\theta_1\in V_1$ satisfies
--
--   $$(1+\varepsilon)\operatorname{tr}\rho_{\theta_0}^2<(1-\varepsilon)\operatorname{tr}\rho_{\theta_1}^2.$$
--
--   Thus any relative-error estimate distinguishes the two sets. Vectors in these sets need not encode valid states.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: a sufficiently small positive absolute c0, then sufficiently large d and small positive precision → an absolute threshold for c0, every smaller positive c0, then joint dimension and precision thresholds; reason: makes the source sufficiently-small convention explicit and permits one compatible choice across the two lemmas
--   - generalization: standing choice on p.18 that d0, ε0 are chosen such that α < 1/4 → α < 1/4 is also asserted as a conclusion for the chosen thresholds; reason: the source requires its thresholds to give α < 1/4; asserting it adds a true clause and the remaining conclusion is the source's
--   - generalization: there exist sets V_i with Pr(θ ∉ V_i) ≤ .01 whose relative-error estimates distinguish them → the specific sets V_i = {θ | |tr(ρ_θ²) − p_i| ≤ ε/d} of the proof (p.20), with disjoint relative-error intervals (1+ε)P(θ0) < (1−ε)P(θ1); reason: a concrete witness implies the existential claim; disjoint intervals is exactly what lets an ε-accurate estimate distinguish the sets
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 6.4, PDF p.19 = printed p.19

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 6.4, PDF p.19, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem encoding_separation : ∃ cstar : ℝ, 0 < cstar ∧ cstar < 1 ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cstar →
  ∃ (d₀ : ℕ) (ε₀ : ℝ), 1 < d₀ ∧ 0 < ε₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
  priorAlpha c₀ d ε < 1/4 ∧ ∀ E : Encoding d, 
    (∀ i : Fin 2, (gaussianPrior (gaussDim d) (priorV c₀ d ε i))
      (goodPuritySet E c₀ ε i)ᶜ ≤ ENNReal.ofReal (1/100 : ℝ)) ∧
    ∀ (θ₀ θ₁ : Vec (gaussDim d)), θ₀ ∈ goodPuritySet E c₀ ε 0 →
      θ₁ ∈ goodPuritySet E c₀ ε 1 →
      (1+ε)*powerSum (encoded E θ₀) 2 < (1-ε)*powerSum (encoded E θ₁) 2 := by sorry

end IncoherentPurity.Adaptive
