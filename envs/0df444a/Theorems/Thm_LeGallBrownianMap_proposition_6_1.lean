-- Prove2me | Theorems.Thm_LeGallBrownianMap_proposition_6_1
-- name    : LeGallBrownianMap.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:50.227301+00:00
-- url     : https://prove2.me/theorems/f873b9f5-db41-4223-a4d5-872287ee7c7d
-- title:
--   Proposition 6.1 — $D^*\le C_\delta D^{1-\delta}$
-- statement:
--   In the setting of Theorem 2.3, let $\delta\in(0,1)$. There is a random constant $C_\delta$ such that, for all $x,y\in m_\infty$,
--
--   $$
--   D^*(x,y)\le C_\delta\, D(x,y)^{1-\delta}.
--   $$
--
--   This preliminary comparison of the two distances is used in the proof of Theorem 7.2.
--
--   Differences from the source:
--   - encoding: in the setting of Theorem 2.3 ((e, Z, D) a subsequential limit of (5)) → hypothesis IsBDGSubseqLimit p φ e Z D P for a strictly increasing φ; reason: a property of the joint law of (e, Z, D), exactly the setting used in §§3–7
--   - encoding: points x, y of m∞ = [0,1]/≈ and D∗ on m∞ → times s, t ∈ [0,1] representing them, and D∗ on [0,1]; reason: p : [0,1] → m∞ is onto and D∗ is defined on m∞ through representatives (p.18)
--   - encoding: a (random) constant C_δ → almost surely ∃ C (depending on the sample); reason: meaning of a random constant
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Proposition 6.1, p.55

import Mathlib
import Definitions.Def_LeGallBrownianMap_IsBDGSubseqLimit
import Definitions.Def_LeGallBrownianMap_dStar

open MeasureTheory

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2,
Proposition 6.1, p.55: "Let δ ∈ (0, 1). There exists a (random) constant C_δ such that, for every
x, y ∈ m∞, D∗(x, y) ≤ C_δ D(x, y)^{1−δ}." In the setting of Theorem 2.3 (`(e, Z, D)` a
subsequential limit of (5), `m∞ = [0,1]/≈` with distance `D`).

For `p ≥ 2`, every subsequential limit `(e, Z, D)` of (5) and every `δ ∈ (0,1)`: almost surely
there is a constant `C` (depending on the sample) with `D∗(s,t) ≤ C D(s,t)^{1−δ}` for all
`s, t ∈ [0,1]`.

**Formalization Note.** Points of `m∞` are represented by times in `[0,1]`; `D∗` on `m∞` is
`D∗` on `[0,1]` (p.15). "Random constant" = `∀ᵐ ω, ∃ C`. The power is `Real.rpow`; `D ≥ 0`
almost surely, being a limit of rescaled graph distances. -/
theorem proposition_6_1 (p : ℕ) (hp : 2 ≤ p) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (φ : ℕ → ℕ) (e Z : Ω → unitInterval → ℝ)
    (D : Ω → unitInterval → unitInterval → ℝ) (hlim : IsBDGSubseqLimit p φ e Z D P)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ s t : unitInterval,
      dStar (e ω) (Z ω) s t ≤ C * D ω s t ^ (1 - δ) := by sorry

end LeGallBrownianMap
