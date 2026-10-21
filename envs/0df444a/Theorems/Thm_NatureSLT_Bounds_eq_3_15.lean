-- Prove2me | Theorems.Thm_NatureSLT_Bounds_eq_3_15
-- name    : NatureSLT.Bounds.eq_3_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:25.083225+00:00
-- url     : https://prove2.me/theorems/e14a662e-a994-437d-96da-f531e524eda3
-- title:
--   Eq. (3.15) — two-sided risk bound with probability $1 - \eta$ for totally bounded functions
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable totally bounded real functions, $A \le Q(z, \alpha) \le B$, with $A < B$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$. Let $G^{\Lambda, \mathcal B}(2\ell)$ be the growth function of the set of indicators $\theta\{Q(z, \alpha) - \beta\}$, $\alpha \in \Lambda$, $\beta \in (A, B)$, on samples of size $2\ell$, let $0 < \eta < 1$, and put
--   $$\mathcal E = 4\, \frac{G^{\Lambda, \mathcal B}(2\ell) - \ln(\eta/4)}{\ell}. \tag{3.14}$$
--   Then with probability at least $1 - \eta$ the following inequalities hold simultaneously for all $\alpha \in \Lambda$:
--   $$R(\alpha) \le R_{\mathrm{emp}}(\alpha) + \frac{B - A}{2} \sqrt{\mathcal E}, \qquad R_{\mathrm{emp}}(\alpha) - \frac{B - A}{2} \sqrt{\mathcal E} \le R(\alpha).$$
--
--   This is the bound on the generalization ability of learning machines with totally bounded losses, in particular for the function minimizing the empirical risk; it is equivalent to the uniform convergence bound (3.10) and is nontrivial when $\mathcal E < 1$.
--
--   **Formalization Note** "With probability at least $1 - \eta$" is $\mathrm{ofReal}(1 - \eta) \le F^\ell(\cdot)$ for the event that both inequalities hold for every $\alpha$. Measurability is assumed explicitly: each $Q(\cdot, \alpha)$ is measurable and, for every level $t$, the event that some deviation $|R(\alpha) - R_{\mathrm{emp}}(\alpha)|$ exceeds $t$ is measurable. The confidence parameter satisfies $0 < \eta < 1$; $\ln$ is the natural logarithm, and $\mathcal E > 0$ because $G^{\Lambda, \mathcal B} \ge 0$ and $\ln(\eta/4) < 0$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 76, Section 3.4, Eq. (3.14) and Case 1 (A), Eq. (3.15)

import Mathlib
import Definitions.Def_NatureSLT_Bounds_growthFunction
import Definitions.Def_NatureSLT_Bounds_levelIndicators

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Eq. (3.15)** (p. 76, §3.4, Case 1 (A)): for a set of measurable totally bounded functions
`A ≤ Q(z, α) ≤ B`, `α ∈ Λ`, and `𝓔 = 4 (G^{Λ,𝓑}(2ℓ) − ln(η/4))/ℓ` (3.14), with probability at
least `1 − η` simultaneously for all `α`:
`R(α) ≤ R_emp(α) + ((B − A)/2) √𝓔` and `R_emp(α) − ((B − A)/2) √𝓔 ≤ R(α)`. -/
theorem eq_3_15 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (A B : ℝ) (hAB : A < B) (hQA : ∀ α z, A ≤ Q α z) (hQB : ∀ α z, Q α z ≤ B)
    (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hdev : ∀ t : ℝ, MeasurableSet
      {z : Fin ℓ → Z | ∃ α, t < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|})
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    let 𝓔 : ℝ := 4 * (growthFunction (levelIndicators Q A B) (2 * ℓ) - Real.log (η / 4)) / ℓ
    ENNReal.ofReal (1 - η) ≤ (Measure.pi fun _ : Fin ℓ => F)
        {z | ∀ α, ∫ x, Q α x ∂F ≤ (1 / (ℓ : ℝ)) * ∑ i, Q α (z i) + (B - A) / 2 * Real.sqrt 𝓔 ∧
          (1 / (ℓ : ℝ)) * ∑ i, Q α (z i) - (B - A) / 2 * Real.sqrt 𝓔 ≤ ∫ x, Q α x ∂F} := by sorry

end NatureSLT.Bounds
