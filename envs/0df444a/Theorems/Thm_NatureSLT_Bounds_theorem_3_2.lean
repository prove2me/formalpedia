-- Prove2me | Theorems.Thm_NatureSLT_Bounds_theorem_3_2
-- name    : NatureSLT.Bounds.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:14.959986+00:00
-- url     : https://prove2.me/theorems/0c457c44-5782-496e-8342-3b67e2a43e2a
-- title:
--   Theorem 3.2 — the basic inequality for the relative deviation, with annealed entropy
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable indicator functions on $Z$ ($\Lambda$ an arbitrary parameter set). Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ for the risk, i.e. the probability of the event $\{z : Q(z, \alpha) = 1\}$, and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for its frequency on an i.i.d. sample $z_1, \dots, z_\ell$ from $F$, $\ell \ge 1$. Let $H^\Lambda_{\mathrm{ann}}(2\ell) = \ln E N^\Lambda(z_1, \dots, z_{2\ell})$ be the annealed entropy on samples of size $2\ell$. Then for every $\varepsilon > 0$
--   $$P\left\{ \sup_{\alpha \in \Lambda} \frac{\int Q(z, \alpha)\, dF(z) - \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)}{\sqrt{\int Q(z, \alpha)\, dF(z)}} > \varepsilon \right\} \le 4 \exp\left\{ \left( \frac{H^\Lambda_{\mathrm{ann}}(2\ell)}{\ell} - \frac{\varepsilon^2}{4} \right) \ell \right\}.$$
--
--   The deviation is normalized by $\sqrt{R(\alpha)}$, which is close to the standard deviation of the frequency when $R(\alpha)$ is small. The bound therefore gives much tighter confidence intervals for functions with small risk than Theorem 3.1, and is the source of the bounds (3.4), (3.7), (3.11) and (3.17) of the book.
--
--   **Formalization Note** The event "the supremum exceeds $\varepsilon$" is written as "there is an $\alpha$ with $R(\alpha) > 0$ whose normalized deviation exceeds $\varepsilon$"; the supremum is taken over the $\alpha$ with $R(\alpha) > 0$, which excludes the zero denominator (for $R(\alpha) = 0$ the numerator is $\le 0$, so the book's event is unaffected). The book assumes the events it measures to be measurable; this is made explicit: each $Q(\cdot, \alpha)$ is measurable, $N^\Lambda$ is measurable on $Z^{2\ell}$ (so that its expectation is defined), and for every level $t$ the event that some normalized deviation exceeds $t$ is measurable. The sample is $z : \{0, \dots, \ell-1\} \to Z$ under the product measure $F^\ell$, and the probability is compared in $[0, \infty]$ with the real right-hand side.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 70, Theorem 3.2 (Eq. (3.2))

import Mathlib
import Definitions.Def_NatureSLT_Bounds_annealedEntropy

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Theorem 3.2** (p. 70): for a set of measurable indicator functions `Q(z, α)`, `α ∈ Λ`, and an
i.i.d. sample of size `ℓ` from `F`,
`P{sup_α (∫ Q dF − (1/ℓ) Σ Q(zᵢ, α)) / √(∫ Q dF) > ε} ≤ 4 exp{(H^Λ_ann(2ℓ)/ℓ − ε²/4) ℓ}`.
The supremum runs over the `α` with `∫ Q(z, α) dF(z) > 0` (a zero denominator is excluded). -/
theorem theorem_3_2 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hQ01 : ∀ α z, Q α z = 0 ∨ Q α z = 1) (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hN : Measurable fun z : Fin (2 * ℓ) → Z => (numSeparations Q z : ℝ))
    (hdev : ∀ t : ℝ, MeasurableSet
      {z : Fin ℓ → Z | ∃ α, 0 < ∫ x, Q α x ∂F ∧
        t < (∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)) / Real.sqrt (∫ x, Q α x ∂F)})
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin ℓ => F)
        {z | ∃ α, 0 < ∫ x, Q α x ∂F ∧
          ε < (∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)) / Real.sqrt (∫ x, Q α x ∂F)}
      ≤ ENNReal.ofReal (4 * Real.exp ((annealedEntropy F Q (2 * ℓ) / ℓ - ε ^ 2 / 4) * ℓ)) := by sorry

end NatureSLT.Bounds
