-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_fisher_bound
-- name    : IncoherentPurity.Adaptive.fisher_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:07.997093+00:00
-- url     : https://prove2.me/theorems/84495aff-b863-4aa2-a4f8-78750007fe34
-- title:
--   Lemma 6.8 — Transcript Fisher information bound
-- statement:
--   For any parameter-independent adaptive policy making $n\ge0$ noisy linear queries with norm bound $L\ge0$, let $Q_s$ be its seeded transcript law under $N(0,s^2I_D)$, where $s>0$. It is a probability law and
--
--   $$I_s(Q_s)\le4nL^2.$$
--
--   The Fisher information is the extended expectation of the squared logarithmic derivative, so this also asserts its finiteness.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 6.8, PDF p.20 = printed p.20

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 6.8, PDF p.20, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem fisher_bound {D : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : QueryPolicy D Ω)
    (n : ℕ) (L s : ℝ) (hL : IsBoundedQuery P L) (hs : 0 < s) :
  IsProbabilityMeasure (queryLaw P n (s^2)) ∧
  queryFisher P n s ≤ ENNReal.ofReal (4*(n : ℝ)*L^2) := by sorry

end IncoherentPurity.Adaptive
