-- Prove2me | Theorems.Thm_OAI_KadisonKastler_relative_ambient_scalar_of_common_equivs
-- name    : OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:52:50.780047+00:00
-- url     : https://prove2.me/theorems/aa607c88-8763-4204-a405-f9bb32183937
-- title:
--   OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs` of [lean/OAI/Analysis/KadisonKastler/RelativeIrreducibilityTransport.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RelativeIrreducibilityTransport.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open Generator.Tracial`):
--
--   ```lean
--   theorem relative_ambient_scalar_of_common_equivs (hRM : R ≤ M) (hSP : S ≤ P)
--       (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra R ≃⋆ₐ[ℂ] Algebra S)
--       (hcompat : ∀ r, e (coordinateInclusion hRM r) = coordinateInclusion hSP (f r))
--       (hirr : ∀ a : Algebra M,
--         (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
--         ∃ c : ℂ, a = c • (1 : Algebra M))
--       (T : K →L[ℂ] K) (hT : T ∈ P) (hc : ∀ s ∈ S, s * T = T * s) :
--       ∃ c : ℂ, T = c • (1 : K →L[ℂ] K)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Generator.Tracial.coordinateInclusion` (definitions bundle `OAIQ075A003` of this split); `OAI.KadisonKastler.Algebra` (definitions bundle `Q260K002` of this split).
--
--   **Used by.** The proof of `OAI.KadisonKastler.exists_commonTracialPosition_of_matrixStages` of this split imports it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/RelativeIrreducibilityTransport.lean (declaration OAI.KadisonKastler.relative_ambient_scalar_of_common_equivs)

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Definitions.Def_Q260K002

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M R : VonNeumannAlgebra H} {P S : VonNeumannAlgebra K}

theorem relative_ambient_scalar_of_common_equivs (hRM : R ≤ M) (hSP : S ≤ P)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra P) (f : Algebra R ≃⋆ₐ[ℂ] Algebra S)
    (hcompat : ∀ r, e (coordinateInclusion hRM r) = coordinateInclusion hSP (f r))
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (T : K →L[ℂ] K) (hT : T ∈ P) (hc : ∀ s ∈ S, s * T = T * s) :
    ∃ c : ℂ, T = c • (1 : K →L[ℂ] K) := by
  sorry

end

end KadisonKastler

end OAI
end
