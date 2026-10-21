-- Prove2me | Theorems.Thm_NatureSLT_Bounds_eq_3_6
-- name    : NatureSLT.Bounds.eq_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:21.444242+00:00
-- url     : https://prove2.me/theorems/dbe9170c-723d-4fba-9a01-3f1963abfe98
-- title:
--   Eq. (3.6) — the basic inequality for totally bounded real functions
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable **totally bounded** real functions, $A \le Q(z, \alpha) \le B$ for all $z$ and $\alpha$, with $A < B$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$. Let $H^{\Lambda, \mathcal B}_{\mathrm{ann}}(2\ell)$ be the annealed entropy, on samples of size $2\ell$, of the set of indicators
--   $$I(z, \alpha, \beta) = \theta\{Q(z, \alpha) - \beta\}, \qquad \alpha \in \Lambda,\ \beta \in \mathcal B = (A, B),$$
--   with $\theta(u) = 1$ for $u \ge 0$ and $0$ otherwise. Then for every $\varepsilon > 0$
--   $$P\left\{ \sup_{\alpha \in \Lambda} \left| \int Q(z, \alpha)\, dF(z) - \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha) \right| > \varepsilon \right\} \le 4 \exp\left\{ \left( \frac{H^{\Lambda, \mathcal B}_{\mathrm{ann}}(2\ell)}{\ell} - \frac{\varepsilon^2}{(B - A)^2} \right) \ell \right\}.$$
--
--   This extends Theorem 3.1 from indicator functions to bounded real functions; for $Q \in \{0, 1\}$ it coincides with (3.1). Replacing the annealed entropy by the growth function gives the distribution-free bound (3.10).
--
--   **Formalization Note** The event "the supremum exceeds $\varepsilon$" is written as "some $\alpha$ has deviation exceeding $\varepsilon$". Measurability is assumed explicitly: each $Q(\cdot, \alpha)$ is measurable (bounded, hence integrable), the counting function of the set of indicators is measurable on $Z^{2\ell}$, and for every level $t$ the event that some deviation exceeds $t$ is measurable. $A$ and $B$ are any finite bounds with $A < B$ (the book's "Let $A \le Q(z, \alpha) \le B$"); the interval $\mathcal B$ is the open interval $(A, B)$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 74, Section 3.2 (i), Eq. (3.6)

import Mathlib
import Definitions.Def_NatureSLT_Bounds_annealedEntropy
import Definitions.Def_NatureSLT_Bounds_levelIndicators

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Eq. (3.6)** (p. 74, §3.2 (i)): for a set of measurable totally bounded functions
`A ≤ Q(z, α) ≤ B`, `α ∈ Λ`,
`P{sup_α |∫ Q(z, α) dF(z) − (1/ℓ) Σ Q(zᵢ, α)| > ε} ≤ 4 exp{(H^{Λ,𝓑}_ann(2ℓ)/ℓ − ε²/(B − A)²) ℓ}`,
where `H^{Λ,𝓑}_ann` is the annealed entropy of the indicators `θ{Q(z, α) − β}`, `β ∈ (A, B)`. -/
theorem eq_3_6 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (A B : ℝ) (hAB : A < B) (hQA : ∀ α z, A ≤ Q α z) (hQB : ∀ α z, Q α z ≤ B)
    (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hN : Measurable fun z : Fin (2 * ℓ) → Z => (numSeparations (levelIndicators Q A B) z : ℝ))
    (hdev : ∀ t : ℝ, MeasurableSet
      {z : Fin ℓ → Z | ∃ α, t < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|})
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin ℓ => F)
        {z | ∃ α, ε < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|}
      ≤ ENNReal.ofReal (4 * Real.exp
          ((annealedEntropy F (levelIndicators Q A B) (2 * ℓ) / ℓ - ε ^ 2 / (B - A) ^ 2) * ℓ)) := by sorry

end NatureSLT.Bounds
