-- Prove2me | Theorems.Thm_FrechetPrefs_proposition_1
-- name    : FrechetPrefs.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:56.510834+00:00
-- url     : https://prove2.me/theorems/6831fcc5-64a4-4732-ae75-16faa05a5b37
-- title:
--   Proposition 1, p.7 — barycentric expected utility as a quantile integral
-- statement:
--   Let $Q_1,\dots,Q_n\in P_2(\mathbb R)$ have quantile functions $F_i^{-1}$, let $w\in\Delta^{n-1}$, and let $Q_B$ be their barycenter. For every utility $u$ measurable for $Q_B$,
--   $$\mathbb E_{Q_B}[u(X)]=\int_0^1u\Big(\sum_{i=1}^nw_iF_i^{-1}(s)\Big)\,ds.$$
--
--   This reduces the barycentric expected utility to a one-dimensional integral over quantile levels.
--
--   **Formalization Note** The measurability of $u$ is almost-everywhere strong measurability for $Q_B$, which only excludes the case where the left side is undefined.
--
--   Differences from the source:
--   - encoding: a lottery X on (Ω,B) under models Q → the law of X, a probability measure on ℝ; reason: the page itself reduces to measures on ℝ on p.5; X plays no other role
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
--   - encoding: u arbitrary → u almost everywhere strongly measurable for Q_B; reason: this excludes only the case where the expectation is undefined
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), Proposition 1, p.7

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- Proposition 1, p.7 of Petracou–Xepapadeas–Yannacopoulos, manuscript MS-DEC-19-01009-REV: the
barycentric expected utility is the quantile integral
`E_{Q_B}[u(X)] = ∫₀¹ u(∑ᵢ wᵢ Fᵢ⁻¹(s)) ds`.

**Formalization Note.** The models are in `P2`, which the barycenter needs. `u` is only required to
be almost everywhere strongly measurable for `B`, so the left side is not a junk value through
non-measurability. -/
theorem proposition_1 {n : ℕ} (w : Fin n → ℝ) (Q : Fin n → ProbabilityMeasure ℝ)
    (u : ℝ → ℝ) (B : ProbabilityMeasure ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2)
    (hB : IsBarycenter w Q B) (hu : AEStronglyMeasurable u (B : Measure ℝ)) :
    ∫ x, u x ∂(B : Measure ℝ) = ∫ s in Ioo (0 : ℝ) 1, u (∑ i, w i * q (Q i) s) := by sorry

end FrechetPrefs
