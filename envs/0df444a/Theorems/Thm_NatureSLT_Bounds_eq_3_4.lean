-- Prove2me | Theorems.Thm_NatureSLT_Bounds_eq_3_4
-- name    : NatureSLT.Bounds.eq_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:19.511513+00:00
-- url     : https://prove2.me/theorems/149cb9d2-cf1e-4a21-b7df-c9bacfc79a2e
-- title:
--   Eq. (3.4) — the distribution-free relative-deviation inequality with the growth function
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable indicator functions on $Z$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$, and let $G^\Lambda(2\ell)$ be the growth function on samples of size $2\ell$. Then for every distribution $F$ and every $\varepsilon > 0$
--   $$P\left\{ \sup_{\alpha \in \Lambda} \frac{\int Q(z, \alpha)\, dF(z) - \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)}{\sqrt{\int Q(z, \alpha)\, dF(z)}} > \varepsilon \right\} \le 4 \exp\left\{ \left( \frac{G^\Lambda(2\ell)}{\ell} - \frac{\varepsilon^2}{4} \right) \ell \right\}.$$
--
--   This is the distribution-free form of Theorem 3.2, obtained by replacing the annealed entropy by the growth function, which dominates it for every distribution.
--
--   **Formalization Note** The supremum is taken over the $\alpha$ with $R(\alpha) > 0$, which excludes the zero denominator (for $R(\alpha) = 0$ the numerator is $\le 0$); the event "the supremum exceeds $\varepsilon$" is written as "some such $\alpha$ has normalized deviation exceeding $\varepsilon$". Measurability is assumed explicitly: each $Q(\cdot, \alpha)$ is measurable and, for every level $t$, the event that some normalized deviation exceeds $t$ is measurable. The sample is $z : \{0, \dots, \ell-1\} \to Z$ under $F^\ell$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 72, Eq. (3.4)

import Mathlib
import Definitions.Def_NatureSLT_Bounds_growthFunction

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Eq. (3.4)** (p. 72): for any distribution `F` and a set of measurable indicator functions
`Q(z, α)`, `α ∈ Λ`,
`P{sup_α (∫ Q dF − (1/ℓ) Σ Q(zᵢ, α)) / √(∫ Q dF) > ε} ≤ 4 exp{(G^Λ(2ℓ)/ℓ − ε²/4) ℓ}`.
The supremum runs over the `α` with `∫ Q(z, α) dF(z) > 0` (a zero denominator is excluded). -/
theorem eq_3_4 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hQ01 : ∀ α z, Q α z = 0 ∨ Q α z = 1) (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hdev : ∀ t : ℝ, MeasurableSet
      {z : Fin ℓ → Z | ∃ α, 0 < ∫ x, Q α x ∂F ∧
        t < (∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)) / Real.sqrt (∫ x, Q α x ∂F)})
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin ℓ => F)
        {z | ∃ α, 0 < ∫ x, Q α x ∂F ∧
          ε < (∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)) / Real.sqrt (∫ x, Q α x ∂F)}
      ≤ ENNReal.ofReal (4 * Real.exp ((growthFunction Q (2 * ℓ) / ℓ - ε ^ 2 / 4) * ℓ)) := by sorry

end NatureSLT.Bounds
