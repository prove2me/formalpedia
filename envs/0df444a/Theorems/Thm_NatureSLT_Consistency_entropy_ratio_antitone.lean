-- Prove2me | Theorems.Thm_NatureSLT_Consistency_entropy_ratio_antitone
-- name    : NatureSLT.Consistency.entropy_ratio_antitone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:47.61111+00:00
-- url     : https://prove2.me/theorems/edcb49b6-7ea7-4615-8828-1afbda64f9d4
-- title:
--   Section 2.6.1 — $H^\Lambda(\ell)/\ell$ decreases monotonically in $\ell$
-- statement:
--   Let $Q(z,\alpha)$, $\alpha\in\Lambda$, be a set of indicator functions on $Z$, $F$ a probability measure on $Z$, and $H^\Lambda(\ell)=E\ln N^\Lambda(z_1,\dots,z_\ell)$ the entropy of the set on i.i.d. samples of size $\ell$ from $F$, where $N^\Lambda(z_1,\dots,z_\ell)$ is the number of different separations of the sample by the set. Then the ratio of the entropy to the number of observations decreases monotonically as $\ell$ increases: for all $1\le \ell \le \ell'$,
--
--   $$\frac{H^\Lambda(\ell')}{\ell'} \le \frac{H^\Lambda(\ell)}{\ell}.$$
--
--   In particular the limit $\lim_{\ell\to\infty}H^\Lambda(\ell)/\ell$ exists, and if it equals $\ln 2$ then $H^\Lambda(\ell)=\ell\ln 2$ for every $\ell$: almost every sample is separated in all $2^\ell$ ways (complete nonfalsifiability).
--
--   **Formalization Note** "Monotonically decreases" is read as non-increasing (the ratio is constant, $\ln 2$, for a set that separates every sample in all ways). The functions are assumed $\{0,1\}$-valued and $N^\Lambda$ a measurable function of the sample for every $\ell$. Logarithms are natural.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 50, Section 2.6.1

import Mathlib
import Definitions.Def_NatureSLT_Consistency_indicatorEntropy

open MeasureTheory

namespace NatureSLT.Consistency

/-- Section 2.6.1 (Vapnik 2000, p. 50): for a set of indicator functions `Q(z, α) ∈ {0, 1}`,
`α ∈ Λ`, the ratio `H^Λ(ℓ)/ℓ` of the entropy to the number of observations decreases
monotonically (non-strictly) as `ℓ ≥ 1` increases. `hN`: the number `N^Λ(z₁, …, z_ℓ)` of
separations is a measurable function of the sample, so that its expectations are genuine. -/
theorem entropy_ratio_antitone {Z Λ : Type*} [MeasurableSpace Z] (F : Measure Z)
    [IsProbabilityMeasure F] (Q : Λ → Z → ℝ) (hQ : ∀ α z, Q α z = 0 ∨ Q α z = 1)
    (hN : ∀ ℓ : ℕ, Measurable (fun z : Fin ℓ → Z => (diversity Q z : ℝ))) :
    AntitoneOn (fun ℓ : ℕ => entropy F Q ℓ / (ℓ : ℝ)) (Set.Ici 1) := by sorry

end NatureSLT.Consistency
