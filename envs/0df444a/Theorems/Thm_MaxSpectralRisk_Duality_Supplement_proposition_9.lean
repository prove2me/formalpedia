-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_proposition_9
-- name    : MaxSpectralRisk.Duality.Supplement.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:12:36.707069+00:00
-- url     : https://prove2.me/theorems/3aac0c28-280b-49cf-9171-df49061861d6
-- title:
--   Proposition 9 (used in the proof of Theorem 2) — lower hemicontinuity
-- statement:
--   Fix $\alpha\in(0,1)$ and a Polish space $\mathcal W$. With the weak topology on its probability measures, the correspondence
--   $$
--   \pi\longmapsto G_\alpha(\pi)
--   $$
--   is lower hemicontinuous on the whole space: if an open set meets $G_\alpha(\pi)$, it meets every sufficiently nearby envelope. This is the lower half of Theorem 2.
--
--   Differences from the source:
--   - encoding: Polish W and weak convergence of probability laws → ProbabilityMeasure W with its weak topology and Borel measurable structure; reason: this is precisely narrow convergence; every source product space satisfies the typeclass assumptions
--   - encoding: Definition 2 lower hemicontinuity → the open-set neighbourhood definition IsLHC; reason: neighbourhoods contain positive-radius balls on the source metric spaces
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 17, Proposition 9

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Correspondence
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory Filter Topology

/-- Proposition 9, p. 17: open-set lower hemicontinuity. -/
theorem proposition_9 {W : Type*} [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    IsLHC (Galpha (W := W) α) := by sorry

end MaxSpectralRisk.Duality.Supplement
