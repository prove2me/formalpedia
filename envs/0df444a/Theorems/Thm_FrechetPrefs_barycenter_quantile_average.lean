-- Prove2me | Theorems.Thm_FrechetPrefs_barycenter_quantile_average
-- name    : FrechetPrefs.barycenter_quantile_average
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:03.309987+00:00
-- url     : https://prove2.me/theorems/a71a1f11-aa95-4de0-aec2-d9297bf3f953
-- title:
--   §2.2, p.6 — the barycenter is the weighted quantile average, exists and is unique
-- statement:
--   Let $Q_1,\dots,Q_n\in P_2(\mathbb R)$ and $w\in\Delta^{n-1}$. Then a barycenter exists; a measure $B\in P_2(\mathbb R)$ is a barycenter exactly when
--   $$F_B^{-1}(s)=\sum_{i=1}^nw_iF_i^{-1}(s)\qquad\text{for all }s\in(0,1);$$
--   and the barycenter is unique.
--
--   This identifies the model $Q_B$ used throughout the mission, and it shows that the hypothesis "$B$ is a barycenter" of the goal theorem is never vacuous.
--
--   Differences from the source:
--   - encoding: models in P(ℝ) → models in P₂(ℝ); reason: the distance of eq. (1) is an L² norm of quantiles: the paper takes Q ⊂ L²([0,1]), p.26, and writes P₂(ℝ) on p.ec6
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), §2.2, p.6

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- §2.2, p.6 of manuscript MS-DEC-19-01009-REV: the Wasserstein barycenter of `Q₁, …, Qₙ` is the
weighted quantile average `F_B⁻¹ = ∑ᵢ wᵢ Fᵢ⁻¹`. A barycenter exists, a measure in `P₂` is a barycenter
exactly when its quantile is this average on `(0,1)`, and the barycenter is unique. -/
theorem barycenter_quantile_average {n : ℕ} (w : Fin n → ℝ)
    (Q : Fin n → ProbabilityMeasure ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hQ : ∀ i, Q i ∈ P2) :
    (∃ B, IsBarycenter w Q B) ∧
    (∀ B, IsBarycenter w Q B ↔
      B ∈ P2 ∧ ∀ s ∈ Ioo (0 : ℝ) 1, q B s = ∑ i, w i * q (Q i) s) ∧
    (∀ B B', IsBarycenter w Q B → IsBarycenter w Q B' → B = B') := by sorry

end FrechetPrefs
