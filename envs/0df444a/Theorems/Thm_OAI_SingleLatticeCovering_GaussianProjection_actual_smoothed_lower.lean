-- Prove2me | Theorems.Thm_OAI_SingleLatticeCovering_GaussianProjection_actual_smoothed_lower
-- name    : OAI.SingleLatticeCovering.GaussianProjection.actual_smoothed_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T12:53:34.553458+00:00
-- url     : https://prove2.me/theorems/2846178e-44cd-428d-afae-8fb2b0210aa0
-- title:
--   OAI.SingleLatticeCovering.GaussianProjection.actual_smoothed_lower: intermediate lemma from OpenAI, A single-lattice covering bound of order n log n
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SingleLatticeCovering.single_lattice_covering`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A single-lattice covering bound of order n log n*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SingleLatticeCovering.GaussianProjection.actual_smoothed_lower` of [lean/OAI/Geometry/LatticeCovering/ProjectionBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/ProjectionBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SingleLatticeCovering.GaussianProjection`, with `open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial`, `open scoped ENNReal Topology RealInnerProductSpace BigOperators`):
--
--   ```lean
--   theorem actual_smoothed_lower {n k D : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
--       {K : Set (Isotropization.E n)} (hK : IsCompact K) (hc : Convex ℝ K)
--       (μ : Measure (Isotropization.E n)) [IsProbabilityMeasure μ]
--       (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
--       {s r T ε : ℝ} (hs : s^2*(n:ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
--       (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48)
--       (hloss : shellLoss n k s r T ε < 1/(4*fourthMomentConstant))
--       (hloss8 : shellLoss n k s r T ε ≤ 1/8) :
--       ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧ ∃ g : MatrixSpace n D, ∀ y : Isotropization.E D,
--         (3/4)*density (1/(2*u)) y-projectionError n D s r ≤ normalizedProjection μ s r g y
--   ```
--
--   **Definitions.** The statement is written with `OAI.SingleLatticeCovering.GaussianDensity.density`, `OAI.SingleLatticeCovering.GaussianProjection.MatrixSpace`, `OAI.SingleLatticeCovering.GaussianProjection.normalizedProjection`, `OAI.SingleLatticeCovering.GaussianProjection.projectionError`, `OAI.SingleLatticeCovering.GaussianProjection.shellLoss`, `OAI.SingleLatticeCovering.Isotropization.E`, `OAI.SingleLatticeCovering.Isotropization.IsIsotropic` and `OAI.SingleLatticeCovering.Prekopa.fourthMomentConstant` (definitions bundle `OAIB3Sl000` of this split).
--
--   **Used by.** The proof of `OAI.SingleLatticeCovering.single_lattice_covering` of this split imports it.
-- source:
--   OpenAI, A single-lattice covering bound of order n log n, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LatticeCovering/ProjectionBounds.lean (declaration OAI.SingleLatticeCovering.GaussianProjection.actual_smoothed_lower)

import Mathlib
import Definitions.Def_OAIB3Sl000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

theorem actual_smoothed_lower {n k D : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (μ : Measure (Isotropization.E n)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε : ℝ} (hs : s^2*(n:ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48)
    (hloss : shellLoss n k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss n k s r T ε ≤ 1/8) :
    ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧ ∃ g : MatrixSpace n D, ∀ y : Isotropization.E D,
      (3/4)*density (1/(2*u)) y-projectionError n D s r ≤ normalizedProjection μ s r g y := by
  sorry

end SingleLatticeCovering.GaussianProjection

end

end OAI
end
