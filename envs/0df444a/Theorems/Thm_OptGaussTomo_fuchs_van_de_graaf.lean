-- Prove2me | Theorems.Thm_OptGaussTomo_fuchs_van_de_graaf
-- name    : OptGaussTomo.fuchs_van_de_graaf
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:38.01968+00:00
-- url     : https://prove2.me/theorems/2d23fe0f-17df-4be2-abad-68dfeaa26437
-- title:
--   Fuchs–van de Graaf inequality $T(\rho,\sigma)\le P(\rho,\sigma)$
-- statement:
--   For any two density operators $\rho,\sigma$ on a Hilbert space (finite- or infinite-dimensional),
--
--   $$
--   T(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1\ \le\ P(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)^2}.
--   $$
--
--   It transfers every purified-distance upper bound of the mission to the trace distance.
--
--   Differences from the source:
--   - encoding: states ρ, ρ̂ (of the fermionic or bosonic system) → density operators on ℓ²(I) for an arbitrary index type I; reason: the paper applies the inequality to both systems; one statement covers both
--   - encoding: T(ρ, ρ̂) → (BosonicLearn.traceDist ρ ρ̂).toReal; reason: the published trace distance is valued in [0, ∞] and is at most 1 on states
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §1 p.3 (pdf p.3)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_OptGaussTomo_purifiedDist

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

namespace OptGaussTomo

/-- **Fuchs–van de Graaf inequality** `T ≤ P` (Chen, Fanizza, Girardi, Lami, Mele, Walter,
Witteveen, *Optimal tomography of bosonic and fermionic Gaussian states*, arXiv:2607.11847, held
version, sha256 0f7548a2…, §1, p.3): "By the Fuchs–van de Graaf inequality `T(ρ, ρ̂) ≤ P(ρ, ρ̂)`,
the result for the purified distance directly implies the sample complexity upper bound in trace
distance."

**Formalization Note.** For any two density operators on a Hilbert space with an orthonormal basis
indexed by `I` (finite or infinite; the inequality is used for fermions and for bosons):
`T = ½‖ρ − σ‖₁` (the published `BosonicLearn.traceDist`, valued in `ℝ≥0∞`; on states it is
at most `1`, so the conversion to `ℝ` is faithful) and `P = √(1 − F²)` with the root fidelity (`purifiedDist`). -/
theorem fuchs_van_de_graaf {I : Type} (ρ σ : State I) :
    (BosonicLearn.traceDist ρ.coefficients σ.coefficients).toReal ≤ purifiedDist ρ.coefficients σ.coefficients := by sorry

end OptGaussTomo
