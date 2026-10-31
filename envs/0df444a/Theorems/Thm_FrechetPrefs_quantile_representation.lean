-- Prove2me | Theorems.Thm_FrechetPrefs_quantile_representation
-- name    : FrechetPrefs.quantile_representation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:52.269989+00:00
-- url     : https://prove2.me/theorems/a99f9c16-33db-4be3-b9dd-4d347a9d6d02
-- title:
--   §2.2, p.5 — measures in $P(\mathbb R)$ and their quantile functions
-- statement:
--   (1) For every probability measure $\mu$ on $\mathbb R$, the quantile $F^{-1}$ is nondecreasing and left-continuous on $(0,1)$; the image of Lebesgue measure on $(0,1)$ under $F^{-1}$ is $\mu$; and $\mu\in P_2(\mathbb R)$ exactly when $F^{-1}\in L^2(0,1)$.
--
--   (2) Conversely, if $g:(0,1)\to\mathbb R$ is nondecreasing, left-continuous and in $L^2(0,1)$, then the image $\mu$ of Lebesgue measure under $g$ is in $P_2(\mathbb R)$, and its quantile function is $g$ on $(0,1)$.
--
--   This correspondence turns the optimization over measures in (4) into one over functions on $(0,1)$. Part (1) uses the published quantile transform.
--
--   Differences from the source:
--   - encoding: quantile functions on [0,1] → quantiles evaluated on the open interval (0,1); reason: the endpoints are null, and F⁻¹(1) can be infinite; no integral changes
-- source:
--   Petracou, Xepapadeas, Yannacopoulos, Decision Making under Model Uncertainty: Fréchet-Wasserstein Mean Preferences, manuscript MS-DEC-19-01009-REV (accepted manuscript, hdl.handle.net/11585/863779), §2.2, p.5

import Mathlib
import Definitions.Def_FrechetPrefs_InadaUtility
import Definitions.Def_FrechetPrefs_Multiplier

open MeasureTheory Set Filter Topology

namespace FrechetPrefs

/-- §2.2, p.5 of manuscript MS-DEC-19-01009-REV: a probability measure on `ℝ` is represented by its
quantile function, and conversely.

(1) For every `μ`, the quantile `q μ` is nondecreasing and left-continuous on `(0,1)`, its law under
Lebesgue measure on `(0,1)` is `μ`, and `μ ∈ P₂` exactly when `q μ ∈ L²(0,1)`.
(2) A nondecreasing, left-continuous `g ∈ L²(0,1)` is the quantile of its law, and that law is in
`P₂`.

**Formalization Note.** `Measure.map` needs a measurable map; on `(0,1)` monotonicity gives almost
everywhere measurability, so these are not the junk zero measure. In (2), `g` is unconstrained off
`(0,1)`. -/
theorem quantile_representation :
    (∀ μ : ProbabilityMeasure ℝ,
      MonotoneOn (q μ) (Ioo 0 1) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ContinuousWithinAt (q μ) (Ioc 0 s) s) ∧
      (volume.restrict (Ioo (0 : ℝ) 1)).map (q μ) = (μ : Measure ℝ) ∧
      (μ ∈ P2 ↔ IntegrableOn (fun s => (q μ s) ^ 2) (Ioo 0 1))) ∧
    (∀ g : ℝ → ℝ, MonotoneOn g (Ioo 0 1) →
      (∀ s ∈ Ioo (0 : ℝ) 1, ContinuousWithinAt g (Ioc 0 s) s) →
      IntegrableOn (fun s => (g s) ^ 2) (Ioo 0 1) →
      ∃ μ : ProbabilityMeasure ℝ,
        (μ : Measure ℝ) = (volume.restrict (Ioo (0 : ℝ) 1)).map g ∧
        μ ∈ P2 ∧ ∀ s ∈ Ioo (0 : ℝ) 1, q μ s = g s) := by sorry

end FrechetPrefs
