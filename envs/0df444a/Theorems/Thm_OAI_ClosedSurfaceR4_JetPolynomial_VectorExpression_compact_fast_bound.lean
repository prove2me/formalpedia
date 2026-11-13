-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_VectorExpression_compact_fast_bound
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_fast_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:47:38.361206+00:00
-- url     : https://prove2.me/theorems/2f34ad86-e344-44c5-a0b9-aa849b727115
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_fast_bound: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_fast_bound` of [lean/OAI/Geometry/SurfaceImmersion/Atlas/FastPhaseBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/FastPhaseBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression`, with `open scoped ContDiff Topology`, `open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector`):
--
--   ```lean
--   theorem compact_fast_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
--       (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
--       (R : VectorExpression) (hRs : R.SmoothCoeffs O) (i : Fin 4)
--       (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
--       ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
--         0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
--         Set.MapsTo (lowJet G) S K →
--         WeightedBound S s (m + (R i).order) B (lowJet G) →
--         ∀ (U : Family S R4), Represents G R U →
--           WeightedBound S z m (D / s ^ (R i).loss)
--             (fun p => U.fastValue ℓ z p i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.order` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.R4` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression` and `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.SmoothCoeffs` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fastValue` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Atlas/FastPhaseBounds.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_fast_bound)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

theorem compact_fast_bound {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (R : VectorExpression) (hRs : R.SmoothCoeffs O) (i : Fin 4)
    (ℓ : Base →L[ℝ] ℝ) (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (s z : ℝ),
      0 < z → z ≤ s → s ≤ 1 → ContDiff ℝ ∞ G →
      Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (R i).order) B (lowJet G) →
      ∀ (U : Family S R4), Represents G R U →
        WeightedBound S z m (D / s ^ (R i).loss)
          (fun p => U.fastValue ℓ z p i) := by
  sorry

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end
