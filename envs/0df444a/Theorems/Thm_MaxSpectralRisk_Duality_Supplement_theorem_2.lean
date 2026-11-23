-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_theorem_2
-- name    : MaxSpectralRisk.Duality.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:14:17.217822+00:00
-- url     : https://prove2.me/theorems/3e3f1db1-f637-43bb-bcab-483a419321c1
-- title:
--   Theorem 2 (companion theorem; not used in the proof of the goal) — continuity of the ES envelope
-- statement:
--   Fix $\alpha\in(0,1)$ and a Polish space $\mathcal W$. For the topology of weak convergence on $\mathcal P(\mathcal W)$,
--   $$
--   G_\alpha:\mathcal P(\mathcal W)\rightrightarrows\mathcal P(\mathcal W)
--   \quad\text{is upper and lower hemicontinuous.}
--   $$
--   This companion theorem describes stability of the expected-shortfall feasible envelope as the reference law changes.
--
--   Differences from the source:
--   - encoding: Polish W and weak convergence of probability laws → ProbabilityMeasure W with its weak topology and Borel measurable structure; reason: this is precisely narrow convergence; every source product space satisfies the typeclass assumptions
--   - encoding: continuity of a correspondence in Definition 2 → the conjunction of open-set upper and lower hemicontinuity; reason: both halves are required on the full domain
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 16, Theorem 2

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Correspondence
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory Filter Topology

/-- Theorem 2, p. 16: continuity means both halves of Definition 2. -/
theorem theorem_2 {W : Type*} [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    ContinuousCorrespondence (Galpha (W := W) α) := by sorry

end MaxSpectralRisk.Duality.Supplement
