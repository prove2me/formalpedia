-- Prove2me | Theorems.Thm_OAI_CurrentKS_State_LightPoint_Psi_driftCurvature
-- name    : OAI.CurrentKS.State.LightPoint.Psi_driftCurvature
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:48:58.682396+00:00
-- url     : https://prove2.me/theorems/21fc2516-5600-4f3d-9748-c01cf0298b57
-- title:
--   OAI.CurrentKS.State.LightPoint.Psi_driftCurvature: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.State.LightPoint`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   lemma Psi_driftCurvature [NeZero d] (lam : ℝ) (Γ : Covariance.Mat (2*N)) :
--       p.driftCurvature (p.Psi lam) Γ = p.driftCurvature p.R Γ+lam*p.driftCurvature penalty Γ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Covariance.Mat`, `OAI.CurrentKS.State.LightPoint`, `OAI.CurrentKS.State.penalty`, `OAI.CurrentKS.State.LightPoint.Psi`, `OAI.CurrentKS.State.LightPoint.R` and `OAI.CurrentKS.State.LightPoint.driftCurvature` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.LightPoint.exists_descent_ensemble` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT002

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State.LightPoint
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction CurrentKS.Covariance
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ} (p : LightPoint d N)

lemma Psi_driftCurvature [NeZero d] (lam : ℝ) (Γ : Covariance.Mat (2*N)) :
    p.driftCurvature (p.Psi lam) Γ = p.driftCurvature p.R Γ+lam*p.driftCurvature penalty Γ := by
  sorry

end
end CurrentKS.State.LightPoint

end OAI
end
