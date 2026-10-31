-- Prove2me | Theorems.Thm_InsiderDonations_eq_A6
-- name    : InsiderDonations.eq_A6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:13.66666+00:00
-- url     : https://prove2.me/theorems/7c5bef28-0339-4b63-9557-d2263b834ca0
-- title:
--   (A6), p.A2 — the derivatives of $\Omega=[1+m+n]\tau_o/(\sigma_v^2[(1+m)\tau_o-m(1-\tau_c)])$
-- statement:
--   Let $\sigma_v>0$ and write $A=(1+m)\tau_o-m(1-\tau_c)$, with $m,n,\tau_o,\tau_c$ real and $A\ne0$. The closed form
--   $$
--   \Omega(m,n,\tau_o,\tau_c)=\frac{[1+m+n]\tau_o}{\sigma_v^2[(1+m)\tau_o-m(1-\tau_c)]}
--   $$
--   has the partial derivatives
--   $$
--   \frac{d\Omega}{dm}=\frac{\tau_o[(1+n)(1-\tau_c)-n\tau_o]}{\sigma_v^2A^2},\qquad
--   \frac{d\Omega}{dn}=\frac{\tau_o}{\sigma_v^2A},
--   $$
--   $$
--   \frac{d\Omega}{d\tau_o}=-\frac{m[1+m+n][1-\tau_c]}{\sigma_v^2A^2},\qquad
--   \frac{d\Omega}{d\tau_c}=-\frac{m[1+m+n]\tau_o}{\sigma_v^2A^2},
--   $$
--   and
--   $$
--   \frac{d\Omega}{dm}-\frac{d\Omega}{dn}=\frac{[1+m+n]\tau_o[1-\tau_c-\tau_o]}{\sigma_v^2A^2}.
--   $$
--
--   Under $m>0$, $n\ge0$, $\tau_o>0$, $\tau_c\le\tau_o<1/2$ and $A>0$, the first two values and the difference are positive and the middle two are negative, as printed.
--
--   **Formalization Note** The first four are `HasDerivAt` statements; the difference is stated with `deriv`. These values give the signs in Proposition 3(b) and (c).
--
--   Differences from the source:
--   - generalization: the derivatives and their printed signs at parameters satisfying the standing assumptions → the values at every real $(m,n,\tau_o,\tau_c)$ with $A\ne0$ and $\sigma_v>0$, the signs at every real point with $m>0$, $n\ge0$, $\tau_o>0$, $\tau_c\le\tau_o<1/2$ and $A>0$; reason: the standing assumptions with $\tau_o>0$ give $A>0$, so the source's case is included
--   - reading: $d\Omega/dm$, $d\Omega/dn$ for counts $m,n$ → derivatives of the closed form in real $m,n$; reason: (A6) differentiates the closed form, which is only defined as a function of real variables
--   - encoding: σv, the standard deviation of ṽ → hypothesis 0 < σv; reason: ṽ is genuine noise; Ω divides by σv²
-- source:
--   Arya–Mittendorf–Ramanan, Tax-favored Stock Donations by Corporate Insiders and Consequences for Equity Markets, SSRN 4003698 (preprint, July 2022), Appendix, proof of Proposition 3, (A6) and the display after it, p.A2 (PDF p.24)

import Mathlib
import Definitions.Def_InsiderDonations_Model

open MeasureTheory ProbabilityTheory

namespace InsiderDonations

/-- (A6). Arya–Mittendorf–Ramanan, SSRN 4003698 (preprint), Appendix, proof of Proposition 3,
(A6), p.A2: with `A = (1+m)τo − m(1−τc)`, the closed form `Ω = [1+m+n]τo/(σv²A)` has
`dΩ/dm = τo[(1+n)(1−τc) − nτo]/(σv²A²)`, `dΩ/dn = τo/(σv²A)`,
`dΩ/dτo = −m[1+m+n][1−τc]/(σv²A²)`, `dΩ/dτc = −m[1+m+n]τo/(σv²A²)`, and
`dΩ/dm − dΩ/dn = [1+m+n]τo[1−τc−τo]/(σv²A²)`; these five values are respectively positive,
positive, negative, negative and positive.

**Formalization Note.** `m`, `n` are real variables. The values hold wherever `A ≠ 0`; the signs
are stated under `0 < m`, `0 ≤ n`, `0 < τo`, `τc ≤ τo < 1/2` and `0 < A`, which the standing
assumptions with `0 < τo` imply. -/
theorem eq_A6 (m n τo τc σv : ℝ) (hσv : 0 < σv) (hA : (1 + m) * τo - m * (1 - τc) ≠ 0) :
    HasDerivAt (fun x => OmegaF x n τo τc σv)
      (τo * ((1 + n) * (1 - τc) - n * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) m ∧
    HasDerivAt (fun x => OmegaF m x τo τc σv)
      (τo / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)))) n ∧
    HasDerivAt (fun t => OmegaF m n t τc σv)
      (-(m * (1 + m + n) * (1 - τc)) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) τo ∧
    HasDerivAt (fun t => OmegaF m n τo t σv)
      (-(m * (1 + m + n) * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) τc ∧
    deriv (fun x => OmegaF x n τo τc σv) m - deriv (fun x => OmegaF m x τo τc σv) n =
      (1 + m + n) * τo * (1 - τc - τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) ∧
    (0 < m → 0 ≤ n → 0 < τo → τc ≤ τo → τo < 1 / 2 → 0 < (1 + m) * τo - m * (1 - τc) →
      0 < τo * ((1 + n) * (1 - τc) - n * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) ∧
      0 < τo / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc))) ∧
      -(m * (1 + m + n) * (1 - τc)) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) < 0 ∧
      -(m * (1 + m + n) * τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2) < 0 ∧
      0 < (1 + m + n) * τo * (1 - τc - τo) / (σv ^ 2 * ((1 + m) * τo - m * (1 - τc)) ^ 2)) := by sorry

end InsiderDonations
