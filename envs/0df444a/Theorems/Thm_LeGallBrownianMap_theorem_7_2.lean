-- Prove2me | Theorems.Thm_LeGallBrownianMap_theorem_7_2
-- name    : LeGallBrownianMap.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:15.370308+00:00
-- url     : https://prove2.me/theorems/e9f30c55-8a10-4140-8752-ff552c98b8c8
-- title:
--   Theorem 7.2 — $D=D^*$ almost surely
-- statement:
--   In the setting of Theorem 2.3, almost surely $D(y,y')=D^*(y,y')$ for all $y,y'\in m_\infty$.
--
--   Together with Theorem 2.3 this identifies every subsequential limit as $(m_\infty,D^*)$, which proves Theorem 1.1 in the bipartite case $q=2p$.
--
--   Differences from the source:
--   - encoding: in the setting of Theorem 2.3 ((e, Z, D) a subsequential limit of (5)) → hypothesis IsBDGSubseqLimit p φ e Z D P for a strictly increasing φ; reason: a property of the joint law of (e, Z, D), exactly the setting used in §§3–7
--   - encoding: points x, y of m∞ = [0,1]/≈ and D∗ on m∞ → times s, t ∈ [0,1] representing them, and D∗ on [0,1]; reason: p : [0,1] → m∞ is onto and D∗ is defined on m∞ through representatives (p.18)
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Theorem 7.2, p.59

import Mathlib
import Definitions.Def_LeGallBrownianMap_IsBDGSubseqLimit
import Definitions.Def_LeGallBrownianMap_dStar

open MeasureTheory

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Theorem 7.2,
p.59: "We have D(y, y′) = D∗(y, y′) for every y, y′ ∈ m∞, almost surely." In the setting of
Theorem 2.3: `(e, Z, D)` is a subsequential limit in distribution of the rescaled contour, label
and distance processes (5) of uniform labeled p-trees, `m∞ = [0,1]/≈` with the distance `D`.

For `p ≥ 2`, every strictly increasing sequence `φ` and every random triple `(e, Z, D)` that is the
limit in distribution of (5) along `φ`: almost surely, `D(s,t) = D∗(s,t)` for all
`s, t ∈ [0,1]`.

**Formalization Note.** Points of `m∞ = [0,1]/≈` are represented by times `s ∈ [0,1]`, and `D∗`
is viewed on `[0,1]` (p.15), so the identity on `m∞` is the identity for all pairs of times. "The
setting of Theorem 2.3" is `IsBDGSubseqLimit p φ e Z D P`, a property of the joint law of
`(e, Z, D)`. One null set for all `s, t`. -/
theorem theorem_7_2 (p : ℕ) (hp : 2 ≤ p) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (φ : ℕ → ℕ) (e Z : Ω → unitInterval → ℝ)
    (D : Ω → unitInterval → unitInterval → ℝ) (hlim : IsBDGSubseqLimit p φ e Z D P) :
    ∀ᵐ ω ∂P, ∀ s t : unitInterval, D ω s t = dStar (e ω) (Z ω) s t := by sorry

end LeGallBrownianMap
