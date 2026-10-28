-- Prove2me | Theorems.Thm_OAI_SK_Analytic_matrixFiniteInterpolation_offset
-- name    : OAI.SK.Analytic.matrixFiniteInterpolation_offset
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:57:29.787143+00:00
-- url     : https://prove2.me/theorems/1c755b21-cd5f-42f5-a1e1-da1bb83a0435
-- title:
--   OAI.SK.Analytic.matrixFiniteInterpolation_offset: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.matrixFiniteInterpolation_offset` of [lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/MatrixGuerraOffset.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/MatrixGuerraOffset.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem matrixFiniteInterpolation_offset {M N d r k : ℕ} (hN : 0<N) (hr : 0 < r) (β : ℝ)
--       (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
--       (H : Fin M → S → ℝ) (C : ℝ)
--       (hcov : ∀ s t, (∑ u, H u s*H u t)=
--         ((N:ℝ)*β^2/2)*matrixSquare d (replicaCrossOverlap N d (X s) (X t))-C)
--       (D : Fin d → Fin d → ℝ) (hself : ∀ s, replicaCrossOverlap N d (X s) (X s)=D)
--       (c : S → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
--       let n:=blockDimension M (N*r) k
--       let F:=matrixFieldObservables N d r k β B X
--       let m:=weightedBlockMass M (N*r) k w
--       let I:=blockInterpolationChoice M (N*r) k
--       hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
--         (interpolationCoefficient n I 1))) 0 ≤
--       hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
--         (interpolationCoefficient n I 0))) 0+
--         ((N:ℝ)*β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
--           ∑ j, w j*matrixSquare d (factorPath d r k B j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.ParameterSpace`, `OAI.SK.Analytic.parameterNormedGroup`, `OAI.SK.Analytic.parameterNormedSpace` and `OAI.SK.Analytic.replicaCrossOverlap` (definitions bundle `OAIQ036S000` of this split); `OAI.SK.Analytic.affineLogPartition`, `OAI.SK.Analytic.blockDimension`, `OAI.SK.Analytic.blockInterpolationChoice`, `OAI.SK.Analytic.blockObservable`, `OAI.SK.Analytic.factorPath`, `OAI.SK.Analytic.interpolationCoefficient`, `OAI.SK.Analytic.matrixFieldObservables`, `OAI.SK.Analytic.matrixInner`, `OAI.SK.Analytic.matrixSquare` and `OAI.SK.Analytic.weightedBlockMass` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.hierarchyPressure` (definitions bundle `OAIQ036S002` of this split); `OAI.SK.Analytic.observableExponent` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proofs of `OAI.SK.Analytic.narrowConstrainedPressure_schedule`, `OAI.SK.Analytic.pairMismatch_pressure_gap` and `OAI.SK.Analytic.tripleConstrainedPressure_schedule` of this split import it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Replicas/MatrixGuerraOffset.lean (declaration OAI.SK.Analytic.matrixFiniteInterpolation_offset)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {S : Type} [Fintype S] [Nonempty S]

theorem matrixFiniteInterpolation_offset {M N d r k : ℕ} (hN : 0<N) (hr : 0 < r) (β : ℝ)
    (B : Fin (k+1) → Fin r → Fin d → ℝ) (X : S → Fin N → Fin d → ℝ)
    (H : Fin M → S → ℝ) (C : ℝ)
    (hcov : ∀ s t, (∑ u, H u s*H u t)=
      ((N:ℝ)*β^2/2)*matrixSquare d (replicaCrossOverlap N d (X s) (X t))-C)
    (D : Fin d → Fin d → ℝ) (hself : ∀ s, replicaCrossOverlap N d (X s) (X s)=D)
    (c : S → ℝ) (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1) :
    let n:=blockDimension M (N*r) k
    let F:=matrixFieldObservables N d r k β B X
    let m:=weightedBlockMass M (N*r) k w
    let I:=blockInterpolationChoice M (N*r) k
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 1))) 0 ≤
    hierarchyPressure n m (affineLogPartition c (observableExponent n (blockObservable H F)
      (interpolationCoefficient n I 0))) 0+
      ((N:ℝ)*β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
        ∑ j, w j*matrixSquare d (factorPath d r k B j)) := by
  sorry

end SK.Analytic

end
end

end OAI
end
