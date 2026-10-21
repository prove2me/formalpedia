-- Prove2me | Theorems.Thm_NatureSLT_Bounds_theorem_3_1
-- name    : NatureSLT.Bounds.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:51:35.289128+00:00
-- url     : https://prove2.me/theorems/c211010b-ec8f-4cd4-bcba-b5fce0cd5028
-- title:
--   Theorem 3.1 — the basic inequality of the theory of bounds, with annealed entropy
-- statement:
--   Let $(Z, F)$ be a probability space and $Q(z, \alpha)$, $\alpha \in \Lambda$, a set of measurable indicator functions on $Z$, indexed by an arbitrary parameter set $\Lambda$. Write $R(\alpha) = \int Q(z, \alpha)\, dF(z)$ for the probability of the event $\{z : Q(z, \alpha) = 1\}$ and $R_{\mathrm{emp}}(\alpha) = \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha)$ for its frequency on an i.i.d. sample $z_1, \dots, z_\ell$ drawn from $F$, $\ell \ge 1$. Let
--   $$H^\Lambda_{\mathrm{ann}}(2\ell) = \ln E\, N^\Lambda(z_1, \dots, z_{2\ell})$$
--   be the annealed VC entropy on samples of size $2\ell$, where $N^\Lambda(z_1, \dots, z_{2\ell})$ is the number of different separations of the sample by the set. Then for every $\varepsilon > 0$
--   $$P\left\{ \sup_{\alpha \in \Lambda} \left| \int Q(z, \alpha)\, dF(z) - \frac1\ell \sum_{i=1}^\ell Q(z_i, \alpha) \right| > \varepsilon \right\} \le 4 \exp\left\{ \left( \frac{H^\Lambda_{\mathrm{ann}}(2\ell)}{\ell} - \varepsilon^2 \right) \ell \right\}. \tag{3.1}$$
--
--   This is the first of the two basic inequalities of the theory of bounds (Vapnik and Chervonenkis): a bound on the rate of uniform convergence of frequencies to probabilities over the whole set, nontrivial (tending to zero as $\ell \to \infty$ for every $\varepsilon > 0$) when $H^\Lambda_{\mathrm{ann}}(\ell)/\ell \to 0$. All the distribution-free and constructive bounds of the chapter descend from it.
--
--   **Formalization Note** The event "the supremum exceeds $\varepsilon$" is written as "some $\alpha$ has deviation exceeding $\varepsilon$", which avoids a supremum over $\Lambda$. The book assumes the events it measures to be measurable; this is made explicit: each $Q(\cdot, \alpha)$ is measurable, $N^\Lambda$ is measurable on $Z^{2\ell}$ (so that its expectation, and hence $H^\Lambda_{\mathrm{ann}}(2\ell)$, is defined), and for every level $t$ the event that some deviation exceeds $t$ is measurable. The sample is $z : \{0, \dots, \ell-1\} \to Z$ under the product measure $F^\ell$, and the probability is compared in $[0, \infty]$ with the real right-hand side. The constants $4$ and $\varepsilon^2$ are the book's, and no condition on $\ell$ other than $\ell \ge 1$ is imposed.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 70, Theorem 3.1 (Eq. (3.1))

import Mathlib
import Definitions.Def_NatureSLT_Bounds_annealedEntropy

open MeasureTheory

namespace NatureSLT.Bounds

/-- **Theorem 3.1** (p. 70): for a set of measurable indicator functions `Q(z, α)`, `α ∈ Λ`, and an
i.i.d. sample of size `ℓ` from `F`,
`P{sup_α |∫ Q(z, α) dF(z) − (1/ℓ) Σ Q(zᵢ, α)| > ε} ≤ 4 exp{(H^Λ_ann(2ℓ)/ℓ − ε²) ℓ}`.
The event "the supremum exceeds `ε`" is written as "some `α` has deviation exceeding `ε`"; its
measurability (for every level `t`) and that of `N^Λ` on samples of size `2ℓ` are assumed. -/
theorem theorem_3_1 {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z) [IsProbabilityMeasure F]
    (Q : Λ → Z → ℝ) (hQ01 : ∀ α z, Q α z = 0 ∨ Q α z = 1) (hQmeas : ∀ α, Measurable (Q α))
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hN : Measurable fun z : Fin (2 * ℓ) → Z => (numSeparations Q z : ℝ))
    (hdev : ∀ t : ℝ, MeasurableSet
      {z : Fin ℓ → Z | ∃ α, t < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|})
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi fun _ : Fin ℓ => F)
        {z | ∃ α, ε < |∫ x, Q α x ∂F - (1 / (ℓ : ℝ)) * ∑ i, Q α (z i)|}
      ≤ ENNReal.ofReal (4 * Real.exp ((annealedEntropy F Q (2 * ℓ) / ℓ - ε ^ 2) * ℓ)) := by sorry

end NatureSLT.Bounds
