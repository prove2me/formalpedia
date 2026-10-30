-- Prove2me | Theorems.Thm_HellingerSubadd_lemmaA11_eq94
-- name    : HellingerSubadd.lemmaA11_eq94
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:03.400902+00:00
-- url     : https://prove2.me/theorems/fdaa304c-8ac4-456e-8809-6c510d723d30
-- title:
--   Lemma A.11, eq. (94): multiplicative Pinsker-type inequality for Hellinger distance
-- statement:
--   Let $P$ and $Q$ be probability measures on $(\mathcal X,\mathcal F)$, let $R\in\mathbb R$, and let $h:\mathcal X\to\mathbb R$ be measurable with $0\le h(X)\le R$ almost surely under $P$ and under $Q$. Then
--
--   $$
--   \bigl|\mathbb E_P[h(X)]-\mathbb E_Q[h(X)]\bigr|\le\sqrt{2R\bigl(\mathbb E_P[h(X)]+\mathbb E_Q[h(X)]\bigr)\cdot D^2_{\mathrm H}(P,Q)}.
--   $$
--
--   Unlike the additive Pinsker bound, the error scales with the size of the expectations themselves; (95) is its rearranged form.
--
--   Differences from the source:
--   - encoding: h : X → R (expectations E_P[h(X)], E_Q[h(X)]) → h measurable; Bochner integrals ∫ h ∂μ, ∫ h ∂ν; reason: the expectations presuppose measurability; a measurable h bounded a.e. is integrable, so the integrals are the paper's expectations
--   - encoding: D²_H(P, Q) as a real number → (hellingerSq μ ν).toReal; reason: D²_H(P, Q) ≤ 2 for probability measures, so toReal loses nothing
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.11, eq. (94), p. 72

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Lemma A.11, eq. (94) (multiplicative Pinsker-type inequality for Hellinger distance).**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.11, eq. (94), p. 72: "Let P and Q be probability measures on (X, F).
For all h : X → R with 0 ≤ h(X) ≤ R almost surely under P and Q, we have
|E_P[h(X)] − E_Q[h(X)]| ≤ sqrt(2R(E_P[h(X)] + E_Q[h(X)]) · D²_H(P, Q))."

**Formalization Note.** `h` is measurable (the expectations presuppose it); bounded measurable
functions are integrable, so the Bochner integrals are the paper's expectations. The bound
`0 ≤ h ≤ R` holds almost everywhere under each measure separately. `D²_H(P, Q)` enters as a real
number via `toReal`; it is finite (at most `2`) for probability measures. -/
theorem lemmaA11_eq94 {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : α → ℝ) (hh : Measurable h) (R : ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ h x ∧ h x ≤ R) (hν : ∀ᵐ x ∂ν, 0 ≤ h x ∧ h x ≤ R) :
    |∫ x, h x ∂μ - ∫ x, h x ∂ν|
      ≤ Real.sqrt (2 * R * (∫ x, h x ∂μ + ∫ x, h x ∂ν) * (hellingerSq μ ν).toReal) := by sorry

end HellingerSubadd
