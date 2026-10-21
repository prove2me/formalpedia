-- Prove2me | Theorems.Thm_NatureSLT_SRM_eq_4_2
-- name    : NatureSLT.SRM.eq_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:41.009978+00:00
-- url     : https://prove2.me/theorems/2587ef75-10f8-4b90-95c3-2cb20a33f3a0
-- title:
--   Eq. (4.2) — risk bound for unbounded nonnegative functions with light tails (p > 2), VC dimension h, with probability 1 − η
-- statement:
--   Let $F$ be a probability measure on a set $Z$ and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable, integrable, unbounded nonnegative functions, containing an infinite number of elements and satisfying, for a pair $(p, \tau)$ with $p > 2$, the condition (3.19)
--   $$\sup_{\alpha \in \Lambda} \frac{\left(\int Q^p(z, \alpha)\, dF(z)\right)^{1/p}}{\int Q(z, \alpha)\, dF(z)} \le \tau < \infty,$$
--   and whose VC dimension (as a set of real functions, indicators $\theta\{Q(z,\alpha) - \beta\}$, $\beta \in (0, \infty)$) is a finite number $h$ with $1 \le h \le 2\ell$. Write $R(\alpha) = \int Q(z,\alpha)\,dF(z)$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for an i.i.d. sample of size $\ell \ge 1$. Let $0 < \eta < 1$,
--   $$\mathcal E = 4\, \frac{h\left(\ln \frac{2\ell}{h} + 1\right) - \ln(\eta/4)}{\ell}, \qquad a(p) = \sqrt[p]{\frac12 \left(\frac{p-1}{p-2}\right)^{p-1}} .$$
--   Then with probability at least $1 - \eta$, simultaneously for all $\alpha \in \Lambda$,
--   $$R(\alpha) \le \frac{R_{\mathrm{emp}}(\alpha)}{\left(1 - a(p)\, \tau \sqrt{\mathcal E}\right)_+},$$
--   where $(u)_+ = \max(u, 0)$ and the right-hand side is $+\infty$ (no constraint) when $1 - a(p)\tau\sqrt{\mathcal E} \le 0$.
--
--   This is the bound for unbounded functions used by structural risk minimization when the elements of the structure satisfy (4.4).
--
--   **Formalization Note** The ratio in (3.19) is written multiplied out, $(\int Q^p dF)^{1/p} \le \tau \int Q\, dF$ for every $\alpha$, which avoids a zero denominator (if $\int Q\,dF = 0$ both sides vanish); $Q^p$ is assumed integrable so that the integral is genuine. The inequality is asserted only when $1 - a(p)\tau\sqrt{\mathcal E} > 0$, which is the book's convention that the bound is infinite otherwise. The event is assumed measurable, the sample is a function $\{0, \dots, \ell-1\} \to Z$ under $F^\ell$, $\ln$ is natural, and, as for (4.1), $1 \le h \le 2\ell$ is assumed (implicit on the page; outside that range $\mathcal E$ can be negative and $\sqrt{\mathcal E}$ undefined, finding F5). As for (4.1), the statement is made simultaneously for all $\alpha$, following its source in Chapter 3.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 93–94, Eq. (4.2); condition (3.19), p. 77

import Mathlib
import Definitions.Def_NatureSLT_SRM_vcDimReal

open MeasureTheory

namespace NatureSLT.SRM

/-- **Eq. (4.2)** with the VC-dimension `𝓔` (Vapnik, *The Nature of Statistical Learning
Theory*, 2nd ed., pp. 93–94; the setting of Case 3, p. 77): for a set of measurable unbounded
nonnegative functions `0 ≤ Q(z, α)`, `α ∈ Λ`, containing an infinite number of elements and satisfying (3.19)
`sup_α (∫ Q^p dF)^{1/p} / ∫ Q dF ≤ τ` with `p > 2`, whose VC dimension (§3.6, indicators
`θ{Q − β}`, `β ∈ (0, ∞)`) is `h`, `1 ≤ h ≤ 2ℓ` (the range where the book's `ln(2ℓ/h)` term bounds the growth
function), with `𝓔 = 4 (h (ln(2ℓ/h) + 1) − ln(η/4))/ℓ` and
`a(p) = ((1/2) ((p − 1)/(p − 2))^{p − 1})^{1/p}`, with probability at least `1 − η`
simultaneously for all `α`: `R(α) ≤ R_emp(α) / (1 − a(p) τ √𝓔)₊`, a bound that is void
(`+∞`) when `1 − a(p) τ √𝓔 ≤ 0`. The event is assumed measurable. -/
theorem eq_4_2 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hQ0 : ∀ α z, 0 ≤ Q α z) (hQmeas : ∀ α, Measurable (Q α))
    (hQint : ∀ α, Integrable (Q α) F) (hinf : (Set.range Q).Infinite)
    (p τ : ℝ) (hp : 2 < p) (hQp : ∀ α, Integrable (fun z => Q α z ^ p) F)
    (h319 : ∀ α, (∫ z, Q α z ^ p ∂F) ^ (1 / p) ≤ τ * ∫ z, Q α z ∂F)
    (h : ℕ) (hvc : vcDimReal Q 0 ⊤ = h)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hh1 : 1 ≤ h) (hh2 : h ≤ 2 * ℓ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    let 𝓔 : ℝ := 4 * ((h : ℝ) * (Real.log (2 * ℓ / h) + 1) - Real.log (η / 4)) / ℓ
    let a : ℝ := ((1 / 2) * ((p - 1) / (p - 2)) ^ (p - 1)) ^ (1 / p)
    let Remp : Λ → (Fin ℓ → Z) → ℝ := fun α z => (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)
    let S : Set (Fin ℓ → Z) := {z | ∀ α, 0 < 1 - a * τ * Real.sqrt 𝓔 →
      ∫ x, Q α x ∂F ≤ Remp α z / (1 - a * τ * Real.sqrt 𝓔)}
    MeasurableSet S → ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F) S := by sorry

end NatureSLT.SRM
