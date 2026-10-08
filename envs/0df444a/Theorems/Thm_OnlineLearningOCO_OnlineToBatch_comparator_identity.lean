-- Prove2me | Theorems.Thm_OnlineLearningOCO_OnlineToBatch_comparator_identity
-- name    : OnlineLearningOCO.OnlineToBatch.comparator_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:24:33.724277+00:00
-- url     : https://prove2.me/theorems/bdb62447-a048-4d50-90a6-ab0b286085f4
-- title:
--   §5, p. 189 — the average loss of a fixed hypothesis is unbiased for its risk
-- statement:
--   Let $T\ge1$, let $\psi_0,\dots,\psi_{T-1}$ be independent examples, each with law $Q$, and let $c$ be an admissible cost on $S\times\Psi$ with risk $C$. For every fixed $u\in S$,
--   $$\mathbb E\Big[\frac1T\sum_{t} c(u,\psi_t)\Big] = C(u).$$
--
--   This identity turns the comparator term of the regret into the risk of the comparator; it is the step from Theorem 5.1 to Corollary 5.2.
--
--   **Formalization Note** Rounds are numbered $0,\dots,T-1$. "$u$ any vector" is read as $u\in S$, where $c(u,\cdot)$ is defined.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 189, §5, the sentence before Corollary 5.2

import Mathlib
import Definitions.Def_OnlineLearningOCO_OnlineToBatch_Setting

open MeasureTheory

namespace OnlineLearningOCO.OnlineToBatch

/-- Shalev-Shwartz, FnT ML 4(2) (2011), §5, p. 189, the line before Corollary 5.2:
for a fixed hypothesis `u ∈ S` and an i.i.d. sample `ψ₀, …, ψ_{T-1}` with law `Q`,
`𝔼[(1/T) ∑_t c(u, ψ_t)] = C(u)`. -/
theorem comparator_identity {d : ℕ} {Ψ : Type*} [MeasurableSpace Ψ]
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (Q : Measure Ψ) [IsProbabilityMeasure Q] (c : EuclideanSpace ℝ (Fin d) → Ψ → ℝ)
    (hc : IsCost S Q c) (T : ℕ) (hT : 0 < T) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ S) :
    ∫ ψ, (1 / (T : ℝ)) * ∑ t : Fin T, c u (ψ t) ∂(sampleLaw Q T) = risk Q c u := by sorry

end OnlineLearningOCO.OnlineToBatch
