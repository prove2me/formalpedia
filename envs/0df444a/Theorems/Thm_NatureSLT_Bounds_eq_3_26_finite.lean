-- Prove2me | Theorems.Thm_NatureSLT_Bounds_eq_3_26_finite
-- name    : NatureSLT.Bounds.eq_3_26_finite
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:48.803344+00:00
-- url     : https://prove2.me/theorems/ab761de2-d1c3-463c-be9e-ff78942e29e0
-- title:
--   Eq. (3.26) with (3.25) — two-sided risk bound for a finite set of N totally bounded functions
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a finite set of $N \ge 1$ measurable totally bounded real functions, $A \le Q(z, \alpha) \le B$, with $A < B$, indexed by a finite set $\Lambda$ of $N$ elements. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$. Let $0 < \eta < 1$ and
--   $$\mathcal E = 2\, \frac{\ln N - \ln \eta}{\ell}. \tag{3.25}$$
--   Then with probability at least $1 - \eta$ the following inequalities hold simultaneously for all $\alpha \in \Lambda$:
--   $$R(\alpha) \le R_{\mathrm{emp}}(\alpha) + \frac{B - A}{2} \sqrt{\mathcal E}, \qquad R(\alpha) \ge R_{\mathrm{emp}}(\alpha) - \frac{B - A}{2} \sqrt{\mathcal E}. \tag{3.26}$$
--
--   This is the constructive bound of Section 3.7 for a finite set of loss functions, the setting used in Chapter 4 for learning machines with finitely many functions.
--
--   **Formalization Note** The set of functions is indexed by a finite nonempty type $\Lambda$ with $N = |\Lambda|$. "With probability at least $1 - \eta$" is $\mathrm{ofReal}(1 - \eta) \le F^\ell(\cdot)$ for the event that both inequalities hold for every $\alpha$; this event is measurable because $\Lambda$ is finite and each $Q(\cdot, \alpha)$ is measurable. As printed, with $\ln N$, the two-sided statement is expected to be false for small samples (see the mission's finding F1: $N = 1$, $\ell = 2$, $\eta = 0.4$); it is stated exactly as the book prints it.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 83–84, Section 3.7, Eq. (3.25) and Case 1 (A), Eq. (3.26)

import Mathlib

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Eq. (3.26) with (3.25)** (p. 84, §3.7, Case 1 (A), finite set): for a set of `N` measurable
totally bounded functions `A ≤ Q(z, α) ≤ B`, `α ∈ Λ`, `N = |Λ|`, and `𝓔 = 2 (ln N − ln η)/ℓ`,
with probability at least `1 − η` simultaneously for all `α`:
`R(α) ≤ R_emp(α) + ((B − A)/2) √𝓔` and `R(α) ≥ R_emp(α) − ((B − A)/2) √𝓔`. -/
theorem eq_3_26_finite {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    [Fintype Λ] [Nonempty Λ]
    (Q : Λ → Z → ℝ) (A B : ℝ) (hAB : A < B) (hQA : ∀ α z, A ≤ Q α z) (hQB : ∀ α z, Q α z ≤ B)
    (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    let 𝓔 : ℝ := 2 * (Real.log (Fintype.card Λ) - Real.log η) / ℓ
    ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F)
        {z | ∀ α, ∫ x, Q α x ∂F ≤ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i) + (B - A) / 2 * Real.sqrt 𝓔 ∧
          ∫ x, Q α x ∂F ≥ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i) - (B - A) / 2 * Real.sqrt 𝓔} := by sorry

end NatureSLT.Bounds
