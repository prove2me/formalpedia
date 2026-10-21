-- Prove2me | Theorems.Thm_NatureSLT_Bounds_eq_3_3
-- name    : NatureSLT.Bounds.eq_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:27.949141+00:00
-- url     : https://prove2.me/theorems/a9a0650c-b9c8-4e8a-bd8f-ecfd001c657d
-- title:
--   Eq. (3.3) — the distribution-free basic inequality with the growth function
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable indicator functions on $Z$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$, and let $G^\Lambda(2\ell) = \ln \sup_{z_1, \dots, z_{2\ell}} N^\Lambda(z_1, \dots, z_{2\ell})$ be the growth function. Then for every distribution $F$ and every $\varepsilon > 0$
--   $$P\left\{ \sup_{\alpha \in \Lambda} \left| \int Q(z, \alpha)\, dF(z) - \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha) \right| > \varepsilon \right\} \le 4 \exp\left\{ \left( \frac{G^\Lambda(2\ell)}{\ell} - \varepsilon^2 \right) \ell \right\}.$$
--
--   The right-hand side no longer depends on $F$: this is the distribution-free form of Theorem 3.1, nontrivial when $G^\Lambda(\ell)/\ell \to 0$, and it is the basis of the constructive bounds of Sections 3.4 and 3.7.
--
--   **Formalization Note** The event "the supremum exceeds $\varepsilon$" is written as "some $\alpha$ has deviation exceeding $\varepsilon$". Measurability, which the book takes for granted, is assumed explicitly: each $Q(\cdot, \alpha)$ is measurable and, for every level $t$, the event that some deviation exceeds $t$ is measurable. The sample is $z : \{0, \dots, \ell-1\} \to Z$ under the product measure $F^\ell$; the growth function is a supremum over all samples of size $2\ell$ and is bounded because $Q$ is $\{0,1\}$-valued.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 72, Eq. (3.3)

import Mathlib
import Definitions.Def_NatureSLT_Bounds_growthFunction

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Eq. (3.3)** (p. 72): for any distribution `F` and a set of measurable indicator functions
`Q(z, α)`, `α ∈ Λ`,
`P{sup_α |∫ Q(z, α) dF(z) − (1/ℓ) Σ Q(zᵢ, α)| > ε} ≤ 4 exp{(G^Λ(2ℓ)/ℓ − ε²) ℓ}`. -/
theorem eq_3_3 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hQ01 : ∀ α z, Q α z = 0 ∨ Q α z = 1) (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hdev : ∀ t : ℝ, MeasurableSet
      {z : Fin ℓ → Z | ∃ α, t < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|})
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin ℓ => F)
        {z | ∃ α, ε < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|}
      ≤ ENNReal.ofReal (4 * Real.exp ((growthFunction Q (2 * ℓ) / ℓ - ε ^ 2) * ℓ)) := by sorry

end NatureSLT.Bounds
