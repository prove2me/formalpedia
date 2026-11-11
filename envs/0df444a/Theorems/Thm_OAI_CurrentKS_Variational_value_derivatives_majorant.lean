-- Prove2me | Theorems.Thm_OAI_CurrentKS_Variational_value_derivatives_majorant
-- name    : OAI.CurrentKS.Variational.value_derivatives_majorant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:55.363108+00:00
-- url     : https://prove2.me/theorems/e01d3f4d-c321-4dd4-b91b-adfa5b5e6c1b
-- title:
--   OAI.CurrentKS.Variational.value_derivatives_majorant: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Variational`, with `open Matrix`, `open CurrentKS.Hermitian Matrix Set Filter`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   theorem value_derivatives_majorant [NeZero d]
--       (ε : ℝ) (hε : 0 < ε) (S : ℝ → H d) (η : ℝ → (H d →L[ℝ] H d)) (a : ℝ)
--       (hS : ContDiffAt ℝ ∞ S a) (hη : ContDiffAt ℝ ∞ η a)
--       (hηpos : ∀ᶠ s in 𝓝 a, ∀ A ∈ psdCone d, η s A ∈ psdCone d)
--       (hηsym : ∀ᶠ s in 𝓝 a, SymmetricMap (η s))
--       {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S a) (hS₂ : S a ≤ K • (Hermitian.one : H d))
--       (z : Point d) (hz : z ∈ feasible (S a) (η a))
--       (hmin : ∀ w ∈ feasible (S a) (η a), objective ε z ≤ objective ε w) :
--       ∃ g : ℝ → Pair d, g a = z.2 ∧ ContDiffAt ℝ ∞ g a ∧
--         (∀ᶠ s in 𝓝 a, residual (S s) (η s) (z.1,g s) = 0) ∧
--         deriv (fun s => value ε (S s) (η s)) a = deriv (fun s => objective ε (z.1,g s)) a ∧
--         deriv (deriv (fun s => value ε (S s) (η s))) a ≤
--           deriv (deriv (fun s => objective ε (z.1,g s))) a
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Variational.Pair`, `OAI.CurrentKS.Variational.Point`, `OAI.CurrentKS.Variational.SymmetricMap`, `OAI.CurrentKS.Variational.feasible`, `OAI.CurrentKS.Variational.objective`, `OAI.CurrentKS.Variational.residual`, `OAI.CurrentKS.Variational.value`, `OAI.CurrentKS.Variational.valueFeasibleOperatorNormedAddCommGroup`, `OAI.CurrentKS.Variational.valueFeasibleOperatorNormedSpace`, `OAI.CurrentKS.Variational.valueFeasiblePairNormedAddCommGroup`, `OAI.CurrentKS.Variational.valueFeasiblePairNormedSpace`, `OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH`, `OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH` and `OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.face_value_direction_variations` of this split imports it.
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

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p8
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedSpace
theorem value_derivatives_majorant [NeZero d]
    (ε : ℝ) (hε : 0 < ε) (S : ℝ → H d) (η : ℝ → (H d →L[ℝ] H d)) (a : ℝ)
    (hS : ContDiffAt ℝ ∞ S a) (hη : ContDiffAt ℝ ∞ η a)
    (hηpos : ∀ᶠ s in 𝓝 a, ∀ A ∈ psdCone d, η s A ∈ psdCone d)
    (hηsym : ∀ᶠ s in 𝓝 a, SymmetricMap (η s))
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S a) (hS₂ : S a ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S a) (η a))
    (hmin : ∀ w ∈ feasible (S a) (η a), objective ε z ≤ objective ε w) :
    ∃ g : ℝ → Pair d, g a = z.2 ∧ ContDiffAt ℝ ∞ g a ∧
      (∀ᶠ s in 𝓝 a, residual (S s) (η s) (z.1,g s) = 0) ∧
      deriv (fun s => value ε (S s) (η s)) a = deriv (fun s => objective ε (z.1,g s)) a ∧
      deriv (deriv (fun s => value ε (S s) (η s))) a ≤
        deriv (deriv (fun s => objective ε (z.1,g s))) a := by
  sorry

end
end CurrentKS.Variational

end OAI
end
