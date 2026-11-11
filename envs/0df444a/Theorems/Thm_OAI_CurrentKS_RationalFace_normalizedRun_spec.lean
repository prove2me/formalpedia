-- Prove2me | Theorems.Thm_OAI_CurrentKS_RationalFace_normalizedRun_spec
-- name    : OAI.CurrentKS.RationalFace.normalizedRun_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:18.211876+00:00
-- url     : https://prove2.me/theorems/4d19d6e0-c504-406e-a12e-e94d9fb77b48
-- title:
--   OAI.CurrentKS.RationalFace.normalizedRun_spec: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.RationalFace`, with `open Matrix`, `open CurrentKS.RationalSDP CurrentKS.Schedule`, `open CurrentKS.Hermitian CurrentKS.State CurrentKS.Difference`, `open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   theorem normalizedRun_spec [NeZero d] [NeZero N]
--       (coords : Fin N → Fin d × Fin d → ℚ)
--       (hA : ∀ i,rationalAtoms coords i∈psdCone d)
--       (hA0 : ∀ i,rationalAtoms coords i≠0)
--       (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
--       (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
--       (∀ i,|normalizedRun coords i|=1) ∧
--         operatorNorm (S (rationalAtoms coords) (pointCast (normalizedRun coords))) ≤
--           40*Real.sqrt (operatorNorm (varianceH (rationalAtoms coords)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.RationalFace.normalizedRun` (definitions bundle `OAIQ241TT000` of this split); `OAI.CurrentKS.Difference.pointCast`, `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.operatorNorm`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.realTrace`, `OAI.CurrentKS.RationalSDP.rationalAtoms`, `OAI.CurrentKS.State.S` and `OAI.CurrentKS.State.varianceH` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.GraphicHalf.half_bounds` of this split imports it.
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

noncomputable section

open Matrix

namespace CurrentKS.RationalFace

open CurrentKS.RationalSDP CurrentKS.Schedule

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.State CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

theorem normalizedRun_spec [NeZero d] [NeZero N]
    (coords : Fin N → Fin d × Fin d → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1) :
    (∀ i,|normalizedRun coords i|=1) ∧
      operatorNorm (S (rationalAtoms coords) (pointCast (normalizedRun coords))) ≤
        40*Real.sqrt (operatorNorm (varianceH (rationalAtoms coords))) := by
  sorry

end CurrentKS.RationalFace

open Matrix

end

end OAI
end
