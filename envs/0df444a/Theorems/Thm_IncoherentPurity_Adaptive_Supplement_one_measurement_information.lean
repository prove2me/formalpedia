-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_Supplement_one_measurement_information
-- name    : IncoherentPurity.Adaptive.Supplement.one_measurement_information
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:52.816949+00:00
-- url     : https://prove2.me/theorems/f5a24b3d-e871-42ab-b052-443b71600c36
-- title:
--   Information in one measurement of a Haar-random spike
-- statement:
--   Let $d$ be any positive integer, let $v$ be a normalized complex Haar-random unit vector in $\mathbb C^d$, and let $M$ be a fixed POVM on an arbitrary measurable outcome space, chosen independently of $v$. Write $p_{\theta,v}$ for its Born outcome law on $\rho_{\theta,v}=(1-\theta)I/d+\theta|v\rangle\langle v|$. For every $s,t\in[0,1)$,
--
--   $$\mathbb E_v D(p_{t,v}\Vert p_{s,v})\le\frac{(t-s)^2}{1-s}\frac{d-1}{d+1}\le\frac{(t-s)^2}{1-s}.$$
--
--   The divergence uses natural logarithms and may take value $+\infty$; the expectation has the same extended nonnegative convention. Both inequalities retain the exact dimension factor, including dimension one, equal parameters, and zero POVM effects. This supplies the one-measurement information estimate for the non-adaptive lower-bound branch.
--
--   Differences from the source:
--   - encoding: Haar-random unit vector and parameters in [0,1) → a trace-one outer-product subtype with the published first-column Haar law, and closed-interval parameters with strict upper bounds; reason: the subtype has exactly the unit vectors and the parameter binders have exactly the source domain
--   - encoding: KL divergence and its Haar expectation → Mathlib natural-log klDiv and a nonnegative extended Lebesgue integral, with ENNReal.ofReal on the finite bounds; reason: preserves infinite divergence and excludes no measurable outcome space; all right-hand sides are nonnegative on the stated domain
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), preprint, pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce; Lemma 5.3, PDF p.16 = printed p.16

import Definitions.Def_IncoherentPurity_Adaptive_Supplement_Spike

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive.Supplement

/-- Lemma 5.3, PDF = printed p.16; pinned source SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem one_measurement_information {d : ℕ} (hd : 0 < d) (H : HaarBasis d)
    {Ω : Type*} [MeasurableSpace Ω] (M : POVM d Ω)
    (s t : Set.Icc (0 : ℝ) 1) (hs : s.val < 1) (ht : t.val < 1) :
    haarInformation hd H M s t ≤
      ENNReal.ofReal ((t.val-s.val)^2 / (1-s.val) * (((d : ℝ)-1)/((d : ℝ)+1))) ∧
    ENNReal.ofReal ((t.val-s.val)^2 / (1-s.val) * (((d : ℝ)-1)/((d : ℝ)+1))) ≤
      ENNReal.ofReal ((t.val-s.val)^2 / (1-s.val)) := by sorry

end IncoherentPurity.Adaptive.Supplement
