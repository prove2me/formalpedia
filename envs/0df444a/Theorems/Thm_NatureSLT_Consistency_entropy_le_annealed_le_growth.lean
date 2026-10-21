-- Prove2me | Theorems.Thm_NatureSLT_Consistency_entropy_le_annealed_le_growth
-- name    : NatureSLT.Consistency.entropy_le_annealed_le_growth
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:46.351806+00:00
-- url     : https://prove2.me/theorems/a97cc047-ec75-4ac0-8ed5-9a6f7baeafca
-- title:
--   Section 2.7 — $H^\Lambda(\ell) \le H^\Lambda_{\mathrm{ann}}(\ell) \le G^\Lambda(\ell)$
-- statement:
--   Let $Q(z,\alpha)$, $\alpha\in\Lambda$, be a set of indicator functions on $Z$, $F$ a probability measure on $Z$, and $N^\Lambda(z_1,\dots,z_\ell)$ the number of different separations of a sample $z_1,\dots,z_\ell$ by the set. With the entropy $H^\Lambda(\ell)=E\ln N^\Lambda(z_1,\dots,z_\ell)$, the annealed VC entropy $H^\Lambda_{\mathrm{ann}}(\ell)=\ln E N^\Lambda(z_1,\dots,z_\ell)$ and the growth function $G^\Lambda(\ell)=\ln\sup_{z_1,\dots,z_\ell}N^\Lambda(z_1,\dots,z_\ell)$, for every $\ell$
--
--   $$H^\Lambda(\ell) \le H^\Lambda_{\mathrm{ann}}(\ell) \le G^\Lambda(\ell).$$
--
--   The ordering is what makes the three milestones of learning theory nested: a condition on the growth function implies the same condition on the annealed entropy, which implies it for the entropy.
--
--   **Formalization Note** The functions are assumed $\{0,1\}$-valued and $N^\Lambda$ a measurable function of the sample, so that both expectations are genuine. Logarithms are natural.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, pp. 55–56, Section 2.7

import Mathlib
import Definitions.Def_NatureSLT_Consistency_indicatorEntropy

open MeasureTheory

namespace NatureSLT.Consistency

/-- Section 2.7 (Vapnik 2000, pp. 55–56): for a set of indicator functions `Q(z, α) ∈ {0, 1}`,
`α ∈ Λ`, and every `ℓ`, `H^Λ(ℓ) ≤ H^Λ_ann(ℓ) ≤ G^Λ(ℓ)`: entropy, annealed VC entropy, growth
function. `hN`: `N^Λ(z₁, …, z_ℓ)` is a measurable function of the sample. -/
theorem entropy_le_annealed_le_growth {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1)
    (hN : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => (diversity Q z : ℝ))) (ℓ : ℕ) :
    entropy F Q ℓ ≤ annealedEntropy F Q ℓ ∧
      annealedEntropy F Q ℓ ≤ growthFunction Q ℓ := by sorry

end NatureSLT.Consistency
