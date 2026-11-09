-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_analytic_factory
-- name    : IncoherentPurity.Adaptive.analytic_factory
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:18.519541+00:00
-- url     : https://prove2.me/theorems/21e69426-e585-4868-a172-49cda2541133
-- title:
--   Theorem A.1 — Analytic Bernoulli factory
-- statement:
--   Let $[a,b]\subset(0,1)$ be a closed interval and let $f$ be real analytic on a neighborhood of that interval, with $0<f(p)<1$ throughout. There is a single stopping coin factory and a constant $0<C_f<\infty$, uniform in the unknown bias $p\in[a,b]$, such that
--
--   $$\Pr(\text{output}=1)=f(p),\qquad\mathbb E[\text{input flips}]\le C_f.$$
--
--   The factory terminates almost surely and only accesses $p$ through independent input flips. The result is attributed in the source to Nacu–Peres, Theorem 2.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: a real analytic function on a closed interval → a real function analytic at every point of the endpoint interval; reason: analytic at a boundary point means analytic on a neighborhood, the usual source convention; values outside the interval are not queried
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Theorem A.1, PDF p.24 = printed p.24

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Theorem A.1, PDF p.24, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem analytic_factory (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc a b, AnalyticAt ℝ f x)
    (hr : ∀ x ∈ Set.Icc a b, 0 < f x ∧ f x < 1) :
  ∃ (F : CoinFactory) (Cf : ℝ), 0 < Cf ∧ ∀ p ∈ Set.Icc a b,
    factoryTerminates F p ∧ factoryTrue F p = ENNReal.ofReal (f p) ∧
    factoryCost F p ≤ ENNReal.ofReal Cf := by sorry

end IncoherentPurity.Adaptive
