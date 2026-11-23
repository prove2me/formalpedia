-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_Supplement_proposition_8
-- name    : MaxSpectralRisk.Duality.Supplement.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:11:01.68981+00:00
-- url     : https://prove2.me/theorems/493d4df4-3d66-47a2-b445-c36fa4779352
-- title:
--   Proposition 8 (used in the proof of Theorem 2) — upper hemicontinuity
-- statement:
--   Fix $\alpha\in(0,1)$ and a Polish space $\mathcal W$. Give $\mathcal P(\mathcal W)$ its weak topology. The risk-envelope correspondence
--   $$
--   \pi\longmapsto G_\alpha(\pi)
--   $$
--   is upper hemicontinuous on all of $\mathcal P(\mathcal W)$: every open set containing $G_\alpha(\pi)$ contains every nearby envelope. This is the upper half of Theorem 2.
--
--   Differences from the source:
--   - encoding: Polish W and weak convergence of probability laws → ProbabilityMeasure W with its weak topology and Borel measurable structure; reason: this is precisely narrow convergence; every source product space satisfies the typeclass assumptions
--   - encoding: Definition 2 upper hemicontinuity on the whole space → the published IsUHC predicate on Set.univ; reason: the open-set neighbourhood formulation is equivalent to the positive-radius ball formulation
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 16, Proposition 8

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Correspondence
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory Filter Topology

/-- Proposition 8, p. 16: upper hemicontinuity on all probability laws. -/
theorem proposition_8 {W : Type*} [TopologicalSpace W] [PolishSpace W]
    [MeasurableSpace W] [BorelSpace W]
    (α : ℝ) (hα : 0 < α ∧ α < 1) :
    CoupledLearning.IsUHC Set.univ (Galpha (W := W) α) := by sorry

end MaxSpectralRisk.Duality.Supplement
