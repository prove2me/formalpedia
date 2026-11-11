-- Prove2me | Theorems.Thm_OAI_CurrentKS_RationalSDP_valuePencil_ball
-- name    : OAI.CurrentKS.RationalSDP.valuePencil_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:11.432366+00:00
-- url     : https://prove2.me/theorems/e6bd2b21-ea8b-4a8a-beb8-3e82d769644d
-- title:
--   OAI.CurrentKS.RationalSDP.valuePencil_ball: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.RationalSDP`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State`, `open Matrix Set`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   lemma valuePencil_ball (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
--       (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
--       (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
--       {ν : ℝ} (hν : ν ≤ 1)
--       (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
--       (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ)))
--       {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
--       Metric.closedBall (packValue (50,(1/20:ℝ) • (Hermitian.one : H d),
--         (1/20:ℝ) • (Hermitian.one : H d))) (valueInnerRadius d:ℝ) ⊆
--         (valuePencil coords x θ ε).feasible
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.RationalSDP.valueDimension`, `OAI.CurrentKS.RationalSDP.valueInnerRadius` and `OAI.CurrentKS.RationalSDP.valuePencil` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.RationalSDP.rationalAtoms`, `OAI.CurrentKS.State.Cube` and `OAI.CurrentKS.State.ParameterCube` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.RationalSDP.packValue` and `OAI.CurrentKS.RationalSDP.Pencil.feasible` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.RationalSDP.valueQueryPoint_correct` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT006

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalSDP
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma valuePencil_ball (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν : ℝ} (hν : ν ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ)))
    {ε : ℚ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Metric.closedBall (packValue (50,(1/20:ℝ) • (Hermitian.one : H d),
      (1/20:ℝ) • (Hermitian.one : H d))) (valueInnerRadius d:ℝ) ⊆
      (valuePencil coords x θ ε).feasible := by
  sorry

end CurrentKS.RationalSDP

end

end OAI
end
