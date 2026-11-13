-- Prove2me | Theorems.Thm_OAI_KadisonKastler_finiteOutwardProjection_integral_lower
-- name    : OAI.KadisonKastler.finiteOutwardProjection_integral_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:47:40.753858+00:00
-- url     : https://prove2.me/theorems/8d12c91c-21d2-4710-be9b-6bdade960506
-- title:
--   OAI.KadisonKastler.finiteOutwardProjection_integral_lower: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.finiteOutwardProjection_integral_lower` of [lean/OAI/Analysis/KadisonKastler/OutwardCutEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OutwardCutEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open MeasureTheory Finset`, `open scoped BigOperators`):
--
--   ```lean
--   theorem finiteOutwardProjection_integral_lower (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
--       ‖((∑ i, (c i : ℂ) • P i)-(∑ j, (d j : ℂ) • Q j)) ξ‖^2 ≤
--         2*(∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.finiteOutwardProjection` (definitions bundle `Q260K007` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_finite_two_vector_projection` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/OutwardCutEnergy.lean (declaration OAI.KadisonKastler.finiteOutwardProjection_integral_lower)

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_Q260K007

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]
  (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
  (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
  (hPo : ∀ i k, i ≠ k → P i*P k=0) (hQo : ∀ j l, j ≠ l → Q j*Q l=0)
  (hPt : ∑ i, P i=1) (hQt : ∑ j, Q j=1) (hc : ∀ i j, Commute (P i) (Q j))

include hP hQ hPo hQo hPt hQt hc

theorem finiteOutwardProjection_integral_lower (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    ‖((∑ i, (c i : ℂ) • P i)-(∑ j, (d j : ℂ) • Q j)) ξ‖^2 ≤
      2*(∫ t, ‖(finiteOutwardProjection P c t-finiteOutwardProjection Q d t) ξ‖^2) := by
  sorry

end

end KadisonKastler

end OAI
end
