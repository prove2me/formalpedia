-- Prove2me | Theorems.Thm_HellingerSubadd_lemmaA10_klDiv_le
-- name    : HellingerSubadd.lemmaA10_klDiv_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:44.153621+00:00
-- url     : https://prove2.me/theorems/c58c6ce0-3cab-434b-9960-7ed85c4c495b
-- title:
--   Lemma A.10 (Yang–Barron), eq. (93): $D_{\mathrm{KL}}(P\|Q)\le(2+\log V)\,D^2_{\mathrm H}(P,Q)$
-- statement:
--   Let $P$ and $Q$ be probability distributions over a measurable space $(\mathcal X,\mathcal F)$, and let $V$ be a real number with
--
--   $$
--   \sup_{F\in\mathcal F}\frac{P(F)}{Q(F)}\le V .
--   $$
--
--   Then
--
--   $$
--   D_{\mathrm{KL}}(P\,\|\,Q)\le\bigl(2+\log V\bigr)\,D^2_{\mathrm H}(P,Q).
--   $$
--
--   This converts a bounded likelihood ratio into a comparison between KL divergence and squared Hellinger distance; in the proof of Lemma A.13 it is applied with $V=1/\lambda$ (Term I) and $V=1/(1-\lambda)$ (Term II).
--
--   Differences from the source:
--   - encoding: sup_{F∈F} P(F)/Q(F) ≤ V → ∀ F, MeasurableSet F → μ F ≤ ENNReal.ofReal V * ν F; reason: the same condition with 0/0 ignored and p/0 = ∞ for p > 0; F = univ forces V ≥ 1
--   - encoding: real-valued KL and (2 + log V) D²_H → klDiv and hellingerSq in ℝ≥0∞, factor ENNReal.ofReal (2 + Real.log V); reason: V ≥ 1 makes 2 + log V positive, so ofReal is exact; klDiv is the paper's KL for probability measures
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.10, eq. (93), p. 72

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory InformationTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Lemma A.10 (Lemma 4 of Yang and Barron (1998)), eq. (93).**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.10, eq. (93), p. 72: "Let P and Q be probability distributions over a
measurable space (X, F). If sup_{F∈F} P(F)/Q(F) ≤ V, then D_KL(P ∥ Q) ≤ (2 + log(V))D²_H(P, Q)."

For probability measures `μ, ν` and a real `V` with `μ(F) ≤ V · ν(F)` for every measurable `F`,
`D_KL(μ ∥ ν) ≤ (2 + log V) · D²_H(μ, ν)`.

**Formalization Note.** The ratio bound `sup_F P(F)/Q(F) ≤ V` is encoded multiplicatively,
`μ F ≤ ENNReal.ofReal V * ν F` for every measurable `F`: the same condition, with `0/0` ignored
and `p/0 = ∞` for `p > 0`. Taking `F = univ` forces `V ≥ 1`, so `2 + log V ≥ 2`. Values in `ℝ≥0∞`;
the real factor enters through `ENNReal.ofReal`; `log` is the natural logarithm. -/
theorem lemmaA10_klDiv_le {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (V : ℝ)
    (hV : ∀ F, MeasurableSet F → μ F ≤ ENNReal.ofReal V * ν F) :
    klDiv μ ν ≤ ENNReal.ofReal (2 + Real.log V) * hellingerSq μ ν := by sorry

end HellingerSubadd
