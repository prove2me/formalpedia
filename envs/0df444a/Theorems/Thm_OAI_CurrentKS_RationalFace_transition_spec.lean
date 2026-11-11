-- Prove2me | Theorems.Thm_OAI_CurrentKS_RationalFace_transition_spec
-- name    : OAI.CurrentKS.RationalFace.transition_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:29.575515+00:00
-- url     : https://prove2.me/theorems/20749e2e-2c1c-459e-a04e-5cab1086945e
-- title:
--   OAI.CurrentKS.RationalFace.transition_spec: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.RationalFace`, with `open Matrix`, `open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent`, `open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar`, `open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   theorem transition_spec [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
--       (hA : ∀ i,rationalAtoms coords i∈psdCone d)
--       (hA0 : ∀ i,rationalAtoms coords i≠0)
--       (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
--       (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
--       {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
--       (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
--         (ν:ℝ) • (Hermitian.one : H d))
--       (x y : Fin N → ℚ) (hx : StripCube (lam^2/ν) x)
--       (hs : transition coords ν lam x=some y) :
--       StripCube (lam^2/ν) y ∧
--         fullPotential coords ν lam y ≤ fullPotential coords ν lam x-(uniformDrop d N ν lam:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.RationalFace.transition` and `OAI.CurrentKS.RationalFace.uniformDrop` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.RationalFace.StripCube`, `OAI.CurrentKS.RationalFace.fullPotential` and `OAI.CurrentKS.RationalSDP.rationalAtoms` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proofs of `OAI.CurrentKS.RationalFace.normalizedRun_spec` and `OAI.CurrentKS.Realization.isPoly_face_orbit` of this split import it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT000
import Definitions.Def_OAIQ241TT002

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
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

theorem transition_spec [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (x y : Fin N → ℚ) (hx : StripCube (lam^2/ν) x)
    (hs : transition coords ν lam x=some y) :
    StripCube (lam^2/ν) y ∧
      fullPotential coords ν lam y ≤ fullPotential coords ν lam x-(uniformDrop d N ν lam:ℝ) := by
  sorry

end
end CurrentKS.RationalFace

end OAI
end
