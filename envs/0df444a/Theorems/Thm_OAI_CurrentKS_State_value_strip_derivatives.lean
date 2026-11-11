-- Prove2me | Theorems.Thm_OAI_CurrentKS_State_value_strip_derivatives
-- name    : OAI.CurrentKS.State.value_strip_derivatives
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:52.000451+00:00
-- url     : https://prove2.me/theorems/8648547b-976b-445d-ae27-c8dcf6a2c30d
-- title:
--   OAI.CurrentKS.State.value_strip_derivatives: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.State`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   theorem value_strip_derivatives [NeZero d] (A : Fin N → H d)
--       (_hA : ∀ i,A i ∈ psdCone d) (hAn : ∀ i,‖A i‖ ≤ 1)
--       (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x h : Coordinates N)
--       {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
--       (hlo : -(100:ℝ) • (Hermitian.one : H d) ≤ S₀+S A x)
--       (hhi : S₀+S A x ≤ (100:ℝ) • (Hermitian.one : H d))
--       (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta 384 A x)) (hz100 : objective ε z ≤ 100)
--       (hmin : ∀ w ∈ feasible (S₀+S A x) (eta 384 A x),objective ε z ≤ objective ε w) :
--       let B := coarseBudget d N ε σ
--       let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
--       let D := 300*B^5
--       let f := fun t : ℝ => value ε (S₀+S A (x+t • h)) (eta 384 A (x+t • h))
--       |iteratedDeriv 2 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*(Jb*D*(1+Jb*D)^2) ∧
--       |iteratedDeriv 3 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*
--         (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.State.Coordinates`, `OAI.CurrentKS.State.S`, `OAI.CurrentKS.State.coarseBudget`, `OAI.CurrentKS.State.eta`, `OAI.CurrentKS.Variational.Point`, `OAI.CurrentKS.Variational.feasible`, `OAI.CurrentKS.Variational.objective`, `OAI.CurrentKS.Variational.value` and `OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.RationalFace.activePotential_regular` of this split imports it.
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

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
private local instance instNormedAddCommGroupVars_r769dcd_1 : NormedAddCommGroup (Vars d) := inferInstance
private local instance instNormedSpaceRealVars_r769dcd_1 : NormedSpace ℝ (Vars d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
theorem value_strip_derivatives [NeZero d] (A : Fin N → H d)
    (_hA : ∀ i,A i ∈ psdCone d) (hAn : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x h : Coordinates N)
    {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2) (hh : ‖h‖ ≤ 1)
    (hlo : -(100:ℝ) • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta 384 A x)) (hz100 : objective ε z ≤ 100)
    (hmin : ∀ w ∈ feasible (S₀+S A x) (eta 384 A x),objective ε z ≤ objective ε w) :
    let B := coarseBudget d N ε σ
    let Jb := 10^18*((d:ℝ)+1)*(1+ε⁻¹)^4
    let D := 300*B^5
    let f := fun t : ℝ => value ε (S₀+S A (x+t • h)) (eta 384 A (x+t • h))
    |iteratedDeriv 2 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*(Jb*D*(1+Jb*D)^2) ∧
    |iteratedDeriv 3 f 0| ≤ (1+|ε| *(2*((d:ℝ)+1)))*
      (Jb*D*((1+Jb*D)^3+3*(1+Jb*D)*(Jb*D*(1+Jb*D)^2))) := by
  sorry
end
end CurrentKS.State

end OAI
end
