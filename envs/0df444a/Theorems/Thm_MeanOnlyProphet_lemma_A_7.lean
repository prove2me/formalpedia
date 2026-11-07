-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_7
-- name    : MeanOnlyProphet.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:22:03.562686+00:00
-- url     : https://prove2.me/theorems/d1d85fcb-380f-40e2-8cb1-2e3389b96da0
-- title:
--   Lemma A.7 — $\mathbb E[e^Z]\,e^{-\mathbb E[Z]}\le e^x/(1+x)$ for $Z$ in an interval of length $x$
-- statement:
--   Let $Z$ be a random variable on a probability space that lies almost surely in an interval of length $x>0$. Then
--   $$
--   \mathbb E\big[e^Z\big]\cdot e^{-\mathbb E[Z]}\ \le\ \frac{e^x}{1+x}.
--   $$
--   It is a reverse Jensen inequality for the exponential, used to compare $\overline P$ with $S$ across a jump of the rate in Lemma A.6.
--
--   Differences from the source:
--   - encoding: Z lies in an interval of length x → Z measurable with Z ∈ [a, a + x] almost surely for some a; reason: every interval of length x lies in the closed one; random variables are measurable
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.7, p.32 (PDF p.33)

import Mathlib

open MeasureTheory

namespace MeanOnlyProphet

/-- **Lemma A.7.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.7, p.32 (PDF p.33): "Let Z be a random variable that lies in an
interval of length x > 0. Then, E[e^Z] · e^{−E[Z]} ≤ e^x/(1 + x)."

**Formalization Note.** `Z` is a measurable real function on a probability space with values almost
surely in a closed interval `[a, a + x]` (this covers every interval of length `x`). Integrability of `Z`
and `e^Z` follows from the bound and is not assumed. -/
theorem lemma_A_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Measurable Z) (x : ℝ) (hx : 0 < x)
    (hZx : ∃ a : ℝ, ∀ᵐ ω ∂P, Z ω ∈ Set.Icc a (a + x)) :
    (∫ ω, Real.exp (Z ω) ∂P) * Real.exp (-∫ ω, Z ω ∂P) ≤ Real.exp x / (1 + x) := by sorry

end MeanOnlyProphet
