-- Prove2me | Theorems.Thm_OAI_CurrentKS_RationalFace_faceCandidates_progress
-- name    : OAI.CurrentKS.RationalFace.faceCandidates_progress
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:01.740027+00:00
-- url     : https://prove2.me/theorems/058e0f59-ed4f-4e0f-8244-489e696fc89d
-- title:
--   OAI.CurrentKS.RationalFace.faceCandidates_progress: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.RationalFace`, with `open Matrix`, `open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent`, `open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar`, `open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff`):
--
--   ```lean
--   lemma faceCandidates_progress [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
--       (base : Fin N → ℚ) [NeZero (activeIndices base).length]
--       (hA : ∀ i,rationalAtoms coords i∈psdCone d)
--       (hA0 : ∀ i,rationalAtoms coords i≠0)
--       (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
--       (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
--       {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
--       (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
--         (ν:ℝ) • (Hermitian.one : H d))
--       (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
--       let p := parameters d (activeIndices base).length ν lam
--       ∃ y∈faceCandidates coords base ν lam,
--         activePotential coords base ν lam (pointCast y) ≤
--           activePotential coords base ν lam (pointCast (faceState base))-2*(p.a:ℝ)*(p.s:ℝ)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.RationalFace.activeIndices`, `OAI.CurrentKS.RationalFace.faceCandidates`, `OAI.CurrentKS.RationalFace.faceState`, `OAI.CurrentKS.Schedule.Parameters` and `OAI.CurrentKS.Schedule.parameters` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Difference.pointCast`, `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich` and `OAI.CurrentKS.RationalSDP.rationalAtoms` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.RationalFace.activePotential` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.RationalFace.transition_spec` of this split imports it.
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

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

lemma faceCandidates_progress [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    ∃ y∈faceCandidates coords base ν lam,
      activePotential coords base ν lam (pointCast y) ≤
        activePotential coords base ν lam (pointCast (faceState base))-2*(p.a:ℝ)*(p.s:ℝ)^2 := by
  sorry

end
end CurrentKS.RationalFace

end OAI
end
