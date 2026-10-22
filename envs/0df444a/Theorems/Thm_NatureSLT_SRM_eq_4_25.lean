-- Prove2me | Theorems.Thm_NatureSLT_SRM_eq_4_25
-- name    : NatureSLT.SRM.eq_4_25
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:58.430548+00:00
-- url     : https://prove2.me/theorems/4bc05e02-917f-4a2e-ac09-0a2ef8b9aa5c
-- title:
--   Eq. (4.25) — risk bound for a finite set of N indicator functions (N tables of a codebook)
-- statement:
--   Let $F$ be a probability measure on a set $Z$ and $Q(z, \alpha)$, $\alpha \in \Lambda$, a finite set of $N \ge 1$ measurable indicator functions (values in $\{0, 1\}$), indexed by a set $\Lambda$ of $N$ elements; in Section 4.6 these are the $N$ decoding tables $T_1, \dots, T_N$ of a codebook, and $Q(z, T_i)$ is the indicator of an error of table $T_i$. Write $R(\alpha) = \int Q(z,\alpha)\,dF(z)$ (the probability of error) and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ (the frequency of training errors) for an i.i.d. sample of size $\ell \ge 1$. Let $0 < \eta < 1$. Then with probability at least $1 - \eta$, simultaneously for all $N$ functions,
--   $$R(\alpha) \le R_{\mathrm{emp}}(\alpha) + \frac{\ln N - \ln \eta}{\ell}\left(1 + \sqrt{1 + \frac{2 R_{\mathrm{emp}}(\alpha)\, \ell}{\ln N - \ln \eta}}\right).$$
--
--   This is the inequality from which the book derives the minimum description length bound (4.27) and Theorem 4.3, by writing $R_{\mathrm{emp}}(T_i) = d/\ell$ for a table making $d$ training errors.
--
--   **Formalization Note** $N = |\Lambda|$; if two indices give the same function the set has fewer than $N$ distinct functions and the statement is weaker, so nothing is lost. Since $\eta < 1$ and $N \ge 1$, $\ln N - \ln \eta > 0$ and no denominator vanishes. The sample is a function $\{0, \dots, \ell-1\} \to Z$ under $F^\ell$; $\ln$ is natural. The event is measurable because $\Lambda$ is finite.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 108, Eq. (4.25)

import Mathlib

open MeasureTheory

namespace NatureSLT.SRM

/-- **Eq. (4.25)** (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., p. 108): for a
learning machine with a finite number `N` of measurable indicator functions `Q(z, α) ∈ {0, 1}`,
`α ∈ Λ`, `N = |Λ|` (the `N` tables of a codebook), with probability at least `1 − η` the
inequality `R(α) ≤ R_emp(α) + ((ln N − ln η)/ℓ) (1 + √(1 + 2 R_emp(α) ℓ/(ln N − ln η)))`
holds simultaneously for all `N` functions. -/
theorem eq_4_25 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    [Fintype Λ] [Nonempty Λ]
    (Q : Λ → Z → ℝ) (hQ01 : ∀ α z, Q α z = 0 ∨ Q α z = 1) (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    let L : ℝ := Real.log (Fintype.card Λ) - Real.log η
    let Remp : Λ → (Fin ℓ → Z) → ℝ := fun α z => (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)
    ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F)
      {z | ∀ α, ∫ x, Q α x ∂F ≤
        Remp α z + L / ℓ * (1 + Real.sqrt (1 + 2 * Remp α z * ℓ / L))} := by sorry

end NatureSLT.SRM
