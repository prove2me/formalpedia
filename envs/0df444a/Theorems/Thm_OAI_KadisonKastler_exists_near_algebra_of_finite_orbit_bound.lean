-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_near_algebra_of_finite_orbit_bound
-- name    : OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:40:41.144012+00:00
-- url     : https://prove2.me/theorems/d06957c5-9201-416e-9e02-934b6d35d3a4
-- title:
--   OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound` of [lean/OAI/Analysis/KadisonKastler/FiniteOrbitDistance.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FiniteOrbitDistance.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Generator`, `open scoped BigOperators InnerProductSpace`):
--
--   ```lean
--   theorem exists_near_algebra_of_finite_orbit_bound
--       (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
--       (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
--       (horbit : ∀ (n : ℕ) (x : FiniteHilbert (Fin n) H),
--         ‖diagonalOperator T x - (tupleOrbitClosure S x).starProjection (diagonalOperator T x)‖ ≤
--           c * ‖x‖)
--       {r : ℝ} (hr : c < r) : ∃ D ∈ S, ‖D - T‖ < r
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.FiniteHilbert` (definitions bundle `OAIQ075A002` of this split); `OAI.Generator.WOTClosed` (definitions bundle `OAIQ075A003` of this split); `OAI.Generator.diagonalOperator`, `OAI.Generator.tupleOrbitClosure` and `OAI.Generator.tupleOrbitClosure_complete` (definitions bundle `OAIQ075A009` of this split).
--
--   **Used by.** The proofs of `OAI.KadisonKastler.constructed_finiteFactor_spatial_of_near_starEquiv`, `OAI.KadisonKastler.finiteFactor_commutant_approx_of_gap`, `OAI.KadisonKastler.publishedBlockCommutantApproximation` and `OAI.KadisonKastler.universal_strong_stability` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/FiniteOrbitDistance.lean (declaration OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound)

import Mathlib
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_OAIQ075A009

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open Generator
open scoped BigOperators InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_near_algebra_of_finite_orbit_bound
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (horbit : ∀ (n : ℕ) (x : FiniteHilbert (Fin n) H),
      ‖diagonalOperator T x - (tupleOrbitClosure S x).starProjection (diagonalOperator T x)‖ ≤
        c * ‖x‖)
    {r : ℝ} (hr : c < r) : ∃ D ∈ S, ‖D - T‖ < r := by
  sorry

end

end KadisonKastler

end OAI
end
