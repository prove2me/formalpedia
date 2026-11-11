-- Prove2me | Theorems.Thm_OAI_CurrentKS_Variational_contDiffAt_value
-- name    : OAI.CurrentKS.Variational.contDiffAt_value
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:05.05149+00:00
-- url     : https://prove2.me/theorems/19fb54b2-1e0a-407e-ab91-52c4d4b9ea10
-- title:
--   OAI.CurrentKS.Variational.contDiffAt_value: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Variational`, with `open Matrix`, `open CurrentKS.Hermitian Matrix Set`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   theorem contDiffAt_value [NeZero d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--       (ε : ℝ) (hε : 0 < ε) (S : E → H d) (η : E → (H d →L[ℝ] H d)) (b : E)
--       (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
--       (hηpos : ∀ A ∈ psdCone d, η b A ∈ psdCone d)
--       (hηsym : ∀ᶠ a in 𝓝 b, SymmetricMap (η a))
--       {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S b) (hS₂ : S b ≤ K • (Hermitian.one : H d))
--       (z : Point d) (hz : z ∈ feasible (S b) (η b))
--       (hmin : ∀ w ∈ feasible (S b) (η b), objective ε z ≤ objective ε w) :
--       ContDiffAt ℝ ∞ (fun a => value ε (S a) (η a)) b
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Variational.Point`, `OAI.CurrentKS.Variational.SymmetricMap`, `OAI.CurrentKS.Variational.feasible`, `OAI.CurrentKS.Variational.objective` and `OAI.CurrentKS.Variational.value` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH`, `OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH` and `OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proofs of `OAI.CurrentKS.RationalFace.activePotential_regular`, `OAI.CurrentKS.State.LightPoint.Psi_driftCurvature`, `OAI.CurrentKS.State.LightPoint.shifted_hessian_not_psd` and `OAI.CurrentKS.Variational.value_derivatives_majorant` of this split import it.
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

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
theorem contDiffAt_value [NeZero d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) (hε : 0 < ε) (S : E → H d) (η : E → (H d →L[ℝ] H d)) (b : E)
    (hS : ContDiffAt ℝ ∞ S b) (hη : ContDiffAt ℝ ∞ η b)
    (hηpos : ∀ A ∈ psdCone d, η b A ∈ psdCone d)
    (hηsym : ∀ᶠ a in 𝓝 b, SymmetricMap (η a))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S b) (hS₂ : S b ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S b) (η b))
    (hmin : ∀ w ∈ feasible (S b) (η b), objective ε z ≤ objective ε w) :
    ContDiffAt ℝ ∞ (fun a => value ε (S a) (η a)) b := by
  sorry

end
end CurrentKS.Variational

end OAI
end
