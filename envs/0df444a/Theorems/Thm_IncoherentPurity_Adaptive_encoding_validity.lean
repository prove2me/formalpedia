-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_encoding_validity
-- name    : IncoherentPurity.Adaptive.encoding_validity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:56.006086+00:00
-- url     : https://prove2.me/theorems/92e7086f-32ed-4647-8c38-b55be5997520
-- title:
--   Lemma 6.3 — Likely validity of Gaussian encodings
-- statement:
--   Choose a sufficiently small positive absolute $c_0<1$, and then sufficiently large $d_0>1$ and small $\varepsilon_0>0$. For every $d\ge d_0$, $0<\varepsilon\le\varepsilon_0$, either prior $i\in\{0,1\}$, and every Hilbert–Schmidt orthonormal real basis of traceless Hermitian matrices, use the parameters (6.5). Then $\alpha<1/4$ and
--
--   $$\Pr_{\theta\sim N(0,v_iI_D)}(\|\Delta_\theta\|_\infty>1/(2d))\le .01.$$
--
--   The Gaussian law is unconditioned and the norm is the operator norm. The sufficiently-small choice is expressed by an absolute threshold valid for every smaller positive $c_0$.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: a sufficiently small positive absolute c0, then sufficiently large d and small positive precision → an absolute threshold for c0, every smaller positive c0, then joint dimension and precision thresholds; reason: makes the source sufficiently-small convention explicit and permits one compatible choice across the two lemmas
--   - generalization: standing choice on p.18 that d0, ε0 are chosen such that α < 1/4 → α < 1/4 is also asserted as a conclusion for the chosen thresholds; reason: the source requires its thresholds to give α < 1/4; asserting it adds a true clause and the remaining conclusion is the source's
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 6.3, PDF p.18 = printed p.18

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 6.3, PDF p.18, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem encoding_validity : ∃ cstar : ℝ, 0 < cstar ∧ cstar < 1 ∧ ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ cstar →
  ∃ (d₀ : ℕ) (ε₀ : ℝ), 1 < d₀ ∧ 0 < ε₀ ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
  priorAlpha c₀ d ε < 1/4 ∧ ∀ E : Encoding d, ∀ i : Fin 2,
    (gaussianPrior (gaussDim d) (priorV c₀ d ε i))
      {θ | opNorm (perturbation E θ) > 1/(2*(d : ℝ))} ≤ ENNReal.ofReal (1/100 : ℝ) := by sorry

end IncoherentPurity.Adaptive
