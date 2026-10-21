-- Prove2me | Theorems.Thm_NatureSLT_SRM_eq_4_1
-- name    : NatureSLT.SRM.eq_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:32.980979+00:00
-- url     : https://prove2.me/theorems/95781724-dcce-487f-a4b6-699be4392160
-- title:
--   Eq. (4.1) — risk bound for totally bounded nonnegative functions of VC dimension h, with probability 1 − η
-- statement:
--   Let $F$ be a probability measure on a set $Z$ and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable totally bounded nonnegative functions, $0 \le Q(z, \alpha) \le B$ with $B > 0$, containing an infinite number of elements, whose VC dimension (as a set of real functions, with indicators $\theta\{Q(z,\alpha) - \beta\}$, $\beta \in (0, B)$) is a finite number $h$ with $1 \le h \le 2\ell$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ for the risk and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for the empirical risk on an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$. Let $0 < \eta < 1$ and
--   $$\mathcal E = 4\, \frac{h\left(\ln \frac{2\ell}{h} + 1\right) - \ln(\eta/4)}{\ell}.$$
--   Then with probability at least $1 - \eta$, simultaneously for all $\alpha \in \Lambda$ (in particular for the function $Q(z, \alpha_\ell)$ minimizing the empirical risk),
--   $$R(\alpha) \le R_{\mathrm{emp}}(\alpha) + \frac{B \mathcal E}{2}\left(1 + \sqrt{1 + \frac{4 R_{\mathrm{emp}}(\alpha)}{B \mathcal E}}\right).$$
--
--   This is the bound for totally bounded functions on which the structural risk minimization principle is built: on each element $S_k$ of a structure it controls the risk by the empirical risk plus a confidence term that grows with the VC dimension.
--
--   **Formalization Note** The sample is a function $\{0, \dots, \ell - 1\} \to Z$ under the product measure $F^\ell$; $\ln$ is the natural logarithm. The event "the inequality holds for all $\alpha$" is assumed measurable (the book's standing "conditions of measurability"); the conclusion is then $F^\ell(\text{event}) \ge 1 - \eta$. The statement assumes $1 \le h \le 2\ell$, which the page leaves implicit: $\ln(2\ell/h)$ is undefined at $h = 0$, and $h(\ln(2\ell/h) + 1)$ bounds the growth function at $2\ell$ only when $2\ell \ge h$; for $h$ much larger than $\ell$ the printed $\mathcal E$ is negative and the printed inequality is false (finding F5: $h = 100$, $\ell = 1$ gives $\mathcal E < 0$ and a right-hand side $B\mathcal E < 0$ for a function with zero risk). The book prints this bound with the empirical minimizer $\alpha_\ell$; following its source (3.17), "simultaneously for all functions (including the function that minimizes the empirical risk)", the statement is made for all $\alpha$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 93–94, Eq. (4.1)

import Mathlib
import Definitions.Def_NatureSLT_SRM_vcDimReal

open MeasureTheory

namespace NatureSLT.SRM

/-- **Eq. (4.1)** with the VC-dimension `𝓔` (Vapnik, *The Nature of Statistical Learning
Theory*, 2nd ed., pp. 93–94): for a set of measurable totally bounded nonnegative functions
`0 ≤ Q(z, α) ≤ B`, `α ∈ Λ`, containing an infinite number of elements, whose VC dimension (§3.6, indicators `θ{Q − β}`, `β ∈ (0, B)`)
is `h`, `1 ≤ h ≤ 2ℓ` (the range where the book's `ln(2ℓ/h)` term bounds the growth
function), and `𝓔 = 4 (h (ln(2ℓ/h) + 1) − ln(η/4))/ℓ`, with probability at least `1 − η`
simultaneously for all `α`:
`R(α) ≤ R_emp(α) + (B𝓔/2) (1 + √(1 + 4 R_emp(α)/(B𝓔)))`.
The event is assumed measurable (the book's standing measurability conditions). -/
theorem eq_4_1 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (B : ℝ) (hB : 0 < B) (hQ0 : ∀ α z, 0 ≤ Q α z) (hQB : ∀ α z, Q α z ≤ B)
    (hQmeas : ∀ α, Measurable (Q α)) (hinf : (Set.range Q).Infinite)
    (h : ℕ) (hvc : vcDimReal Q 0 (B : EReal) = h)
    (ℓ : ℕ) (hℓ : 0 < ℓ) (hh1 : 1 ≤ h) (hh2 : h ≤ 2 * ℓ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    let 𝓔 : ℝ := 4 * ((h : ℝ) * (Real.log (2 * ℓ / h) + 1) - Real.log (η / 4)) / ℓ
    let Remp : Λ → (Fin ℓ → Z) → ℝ := fun α z => (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)
    let S : Set (Fin ℓ → Z) := {z | ∀ α, ∫ x, Q α x ∂F ≤
      Remp α z + B * 𝓔 / 2 * (1 + Real.sqrt (1 + 4 * Remp α z / (B * 𝓔)))}
    MeasurableSet S → ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F) S := by sorry

end NatureSLT.SRM
