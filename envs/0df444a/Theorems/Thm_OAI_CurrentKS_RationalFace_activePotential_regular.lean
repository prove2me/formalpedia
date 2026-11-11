-- Prove2me | Theorems.Thm_OAI_CurrentKS_RationalFace_activePotential_regular
-- name    : OAI.CurrentKS.RationalFace.activePotential_regular
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:55:33.479803+00:00
-- url     : https://prove2.me/theorems/cbe70b36-6680-472b-8cff-d535807ad405
-- title:
--   OAI.CurrentKS.RationalFace.activePotential_regular: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.RationalFace`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar`, `open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference`, `open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff`):
--
--   ```lean
--   lemma activePotential_regular [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
--       (base : Fin N → ℚ) (hA : ∀ i,rationalAtoms coords i∈psdCone d)
--       (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
--       {ν lam σ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hσ : 0 < σ)
--       (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
--         (ν:ℝ) • (Hermitian.one : H d))
--       (hb : ∀ i,|base i| ≤ 1)
--       (hx : ∀ i,|faceState base i| ≤ 1-σ)
--       {r : ℝ} (hr : 0 ≤ r) (hrσ : r ≤ (σ:ℝ)/2)
--       (y : Coordinates (activeIndices base).length) (hy : ‖y-pointCast (faceState base)‖ ≤ r) :
--       ContDiffAt ℝ 3 (activePotential coords base ν lam) y ∧
--         ∀ u,‖u‖ ≤ 1 →
--           |iteratedDeriv 2 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
--             (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) ∧
--           |iteratedDeriv 3 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
--             (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.RationalFace.activeIndices`, `OAI.CurrentKS.RationalFace.faceState` and `OAI.CurrentKS.Schedule.curveBudget` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Difference.pointCast`, `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.RationalSDP.rationalAtoms` and `OAI.CurrentKS.State.Coordinates` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.RationalFace.activePotential` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.RationalFace.faceCandidates_progress` of this split imports it.
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
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

lemma activePotential_regular [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam σ : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hσ : 0 < σ)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1)
    (hx : ∀ i,|faceState base i| ≤ 1-σ)
    {r : ℝ} (hr : 0 ≤ r) (hrσ : r ≤ (σ:ℝ)/2)
    (y : Coordinates (activeIndices base).length) (hy : ‖y-pointCast (faceState base)‖ ≤ r) :
    ContDiffAt ℝ 3 (activePotential coords base ν lam) y ∧
      ∀ u,‖u‖ ≤ 1 →
        |iteratedDeriv 2 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
          (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) ∧
        |iteratedDeriv 3 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤
          (curveBudget d (activeIndices base).length (ν/(d:ℚ)) σ lam:ℝ) := by
  sorry

end
end CurrentKS.RationalFace

end OAI
end
