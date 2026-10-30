-- Prove2me | Theorems.Thm_HellingerSubadd_lemmaA11_eq95
-- name    : HellingerSubadd.lemmaA11_eq95
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:53:36.514503+00:00
-- url     : https://prove2.me/theorems/f3db5457-394a-4c3e-ba39-7d0f2aee0028
-- title:
--   Lemma A.11, eq. (95): $\mathbb E_P[h]\le 3\,\mathbb E_Q[h]+4R\,D^2_{\mathrm H}(P,Q)$
-- statement:
--   Let $P$ and $Q$ be probability measures on $(\mathcal X,\mathcal F)$, let $R\in\mathbb R$, and let $h:\mathcal X\to\mathbb R$ be measurable with $0\le h(X)\le R$ almost surely under $P$ and under $Q$. Then
--
--   $$
--   \mathbb E_P[h(X)]\le3\,\mathbb E_Q[h(X)]+4R\,D^2_{\mathrm H}(P,Q).
--   $$
--
--   In the proof of Lemma A.13 it is applied with $h$ the sum of conditional squared Hellinger distances and $R=2n$, to move an expectation under $\mathbb P$ to one under $\mathbb Q$.
--
--   Differences from the source:
--   - encoding: h : X → R (expectations E_P[h(X)], E_Q[h(X)]) → h measurable; Bochner integrals ∫ h ∂μ, ∫ h ∂ν; reason: the expectations presuppose measurability; a measurable h bounded a.e. is integrable, so the integrals are the paper's expectations
--   - encoding: D²_H(P, Q) as a real number → (hellingerSq μ ν).toReal; reason: D²_H(P, Q) ≤ 2 for probability measures, so toReal loses nothing
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.11, eq. (95), p. 72

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory
open scoped ENNReal

namespace HellingerSubadd

/-- **Lemma A.11, eq. (95).**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.11, eq. (95), p. 72: under the hypotheses of Lemma A.11 (P, Q
probability measures on (X, F), h : X → R with 0 ≤ h(X) ≤ R almost surely under P and Q),
"In particular, E_P[h(X)] ≤ 3 E_Q[h(X)] + 4RD²_H(P, Q)."

**Formalization Note.** As in `lemmaA11_eq94`: `h` measurable, the bound a.e. under each measure,
`D²_H` as a real number via `toReal` (finite for probability measures). -/
theorem lemmaA11_eq95 {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : α → ℝ) (hh : Measurable h) (R : ℝ)
    (hμ : ∀ᵐ x ∂μ, 0 ≤ h x ∧ h x ≤ R) (hν : ∀ᵐ x ∂ν, 0 ≤ h x ∧ h x ≤ R) :
    ∫ x, h x ∂μ ≤ 3 * ∫ x, h x ∂ν + 4 * R * (hellingerSq μ ν).toReal := by sorry

end HellingerSubadd
