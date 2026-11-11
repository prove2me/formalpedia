-- Prove2me | Theorems.Thm_OAI_CurrentKS_RationalSDP_valueQueryPoint_correct
-- name    : OAI.CurrentKS.RationalSDP.valueQueryPoint_correct
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:54:01.447694+00:00
-- url     : https://prove2.me/theorems/6b2b9d59-14d2-49ac-93a2-a8c2dfa4a7dc
-- title:
--   OAI.CurrentKS.RationalSDP.valueQueryPoint_correct: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.RationalSDP`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State`, `open Matrix Set`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   lemma valueQueryPoint_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
--       (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
--       (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
--       {ν δ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
--       (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
--         (ν:ℝ) • (Hermitian.one : H d))
--       (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ))) :
--       let ε : ℚ := ν/d
--       let y := valueQueryPoint coords x θ ν δ
--       realVector y ∈ (valuePencil coords x θ ε).feasible ∧
--         |(valueQuery coords x θ ν δ:ℝ)-value (ε:ℝ)
--           (S (rationalAtoms coords) (fun i => (x i:ℝ)))
--           (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ)))| ≤ 2*(δ:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.RationalSDP.valueDimension`, `OAI.CurrentKS.RationalSDP.valuePencil`, `OAI.CurrentKS.RationalSDP.valueQuery` and `OAI.CurrentKS.RationalSDP.valueQueryPoint` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.RationalSDP.rationalAtoms`, `OAI.CurrentKS.RationalSDP.realVector`, `OAI.CurrentKS.State.Cube`, `OAI.CurrentKS.State.ParameterCube`, `OAI.CurrentKS.State.S`, `OAI.CurrentKS.State.etaTheta` and `OAI.CurrentKS.Variational.value` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.RationalSDP.Pencil.feasible` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proofs of `OAI.CurrentKS.RationalFace.faceCandidates_progress` and `OAI.CurrentKS.RationalFace.transition_spec` of this split import it.
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

lemma valueQueryPoint_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ) (x θ : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν δ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) (hθ : ParameterCube (fun i => (θ i:ℝ))) :
    let ε : ℚ := ν/d
    let y := valueQueryPoint coords x θ ν δ
    realVector y ∈ (valuePencil coords x θ ε).feasible ∧
      |(valueQuery coords x θ ν δ:ℝ)-value (ε:ℝ)
        (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (etaTheta 384 (rationalAtoms coords) (fun i => (θ i:ℝ)))| ≤ 2*(δ:ℝ) := by
  sorry

end CurrentKS.RationalSDP

end

end OAI
end
