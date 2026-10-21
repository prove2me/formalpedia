-- Prove2me | Theorems.Thm_NatureSLT_Consistency_entropy_criterion
-- name    : NatureSLT.Consistency.entropy_criterion
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:36.908808+00:00
-- url     : https://prove2.me/theorems/752687ef-1d67-49ea-a62f-bf04022abd66
-- title:
--   Theorem 2.3 — uniform two-sided convergence iff $H^\Lambda(\varepsilon,\ell)/\ell \to 0$
-- statement:
--   Let $F$ be a probability measure on $Z$ and $A\le Q(z,\alpha)\le B$, $\alpha\in\Lambda$, a set of bounded measurable real functions. Let $H^\Lambda(\varepsilon,\ell)=E\ln N^\Lambda(\varepsilon;z_1,\dots,z_\ell)$ be its VC entropy, where $N^\Lambda(\varepsilon;z_1,\dots,z_\ell)$ is the size of a minimal $\varepsilon$-net, in the metric $C$, of the vectors $(Q(z_1,\alpha),\dots,Q(z_\ell,\alpha))$, $\alpha\in\Lambda$. Then uniform two-sided convergence
--
--   $$\lim_{\ell\to\infty}P\Bigl\{\sup_{\alpha\in\Lambda}\Bigl|\int Q(z,\alpha)\,dF(z)-\frac1\ell\sum_{i=1}^\ell Q(z_i,\alpha)\Bigr|>\varepsilon\Bigr\}=0\qquad\forall\varepsilon>0 \tag{2.6}$$
--
--   holds if and only if
--
--   $$\lim_{\ell\to\infty}\frac{H^\Lambda(\varepsilon,\ell)}{\ell}=0\qquad\forall\varepsilon>0. \tag{2.10}$$
--
--   This is the Vapnik–Chervonenkis (1981) entropy criterion for the law of large numbers in a functional space, generalizing the 1968/1971 criterion for indicator functions; it supplies the conditions from which those of uniform one-sided convergence, and hence of consistency, are built.
--
--   **Formalization Note** The book states the theorem "under some (technical) conditions of measurability". They are made explicit as hypotheses: each $Q(\cdot,\alpha)$ is measurable; for every $\ell$ the supremum $\xi^\ell$ of (2.5), the supremum over $\alpha$ of the difference $\bigl|\frac1\ell\sum_{i=1}^{\ell}Q(z_i,\alpha)-\frac1\ell\sum_{i=\ell+1}^{2\ell}Q(z_i,\alpha)\bigr|$ of the empirical means over the two halves of a sample of size $2\ell$, and, for $\varepsilon>0$, the random VC entropy are measurable functions of the sample. The suprema are taken in the extended reals; probabilities are values of the product measure $F^\ell$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 45, Theorem 2.3, Eq. (2.10)

import Mathlib
import Definitions.Def_NatureSLT_Consistency_risk
import Definitions.Def_NatureSLT_Consistency_uniformConvergence
import Definitions.Def_NatureSLT_Consistency_vcEntropy

open MeasureTheory Filter Topology

namespace NatureSLT.Consistency

/-- **Theorem 2.3** (Vapnik 2000, p. 45). For a set of bounded real functions
`A ≤ Q(z, α) ≤ B`, `α ∈ Λ` (Section 2.3.3, p. 43), uniform two-sided convergence (2.6) holds iff
`lim_{ℓ→∞} H^Λ(ε, ℓ)/ℓ = 0` for every `ε > 0` (2.10), `H^Λ(ε, ℓ)` the VC entropy (ε-nets in the
metric `C`). The book's "some (technical) conditions of measurability" are made explicit:
each `Q(·, α)` is measurable (`hmeas`); the sample functions `ξ^ℓ` (2.5) (`hsup`), the
difference of empirical means over the two halves of a sample of size `2ℓ` (`hsemi`), and the
random VC entropy (`hH`) are measurable. -/
theorem entropy_criterion {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (A B : ℝ)
    (hbdd : ∀ α z, A ≤ Q α z ∧ Q α z ≤ B) (hmeas : ∀ α, Measurable (Q α))
    (hsup : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => supTwoSidedDeviation F Q z))
    (hsemi : ∀ ℓ : ℕ, Measurable (fun z : Fin (ℓ + ℓ) → Z =>
      ⨆ α : Λ, ((|empiricalRisk Q (fun i : Fin ℓ => z (Fin.castAdd ℓ i)) α
        - empiricalRisk Q (fun i : Fin ℓ => z (Fin.natAdd ℓ i)) α| : ℝ) : EReal)))
    (hH : ∀ (ε : ℝ) (ℓ : ℕ), 0 < ε → Measurable (fun z : Fin ℓ → Z => randomVCEntropy Q ε z)) :
    UniformTwoSidedConvergence F Q ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun ℓ : ℕ => vcEntropy F Q ε ℓ / (ℓ : ℝ)) atTop (𝓝 0) := by sorry

end NatureSLT.Consistency
