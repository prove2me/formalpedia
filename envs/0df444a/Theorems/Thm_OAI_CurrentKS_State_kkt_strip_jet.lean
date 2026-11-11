-- Prove2me | Theorems.Thm_OAI_CurrentKS_State_kkt_strip_jet
-- name    : OAI.CurrentKS.State.kkt_strip_jet
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:59.157553+00:00
-- url     : https://prove2.me/theorems/0becf6c6-24ab-4d6f-ba88-ba5012711709
-- title:
--   OAI.CurrentKS.State.kkt_strip_jet: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.State`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   lemma kkt_strip_jet (A : Fin N → H d) (hA : ∀ i,‖A i‖ ≤ 1)
--       (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x : Coordinates N) {ε σ : ℝ}
--       (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2)
--       (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
--       (hz : ‖z‖ ≤ 200+(200/ε)*((d:ℝ)+1))
--       (hiX : ‖invH (xCoord d z)‖ ≤ 200*((d:ℝ)+1))
--       (hiY : ‖invH (yCoord d z)‖ ≤ 200*((d:ℝ)+1))
--       (hP : ‖mCoord d z‖ ≤ 1) (hQ : ‖nCoord d z‖ ≤ 1) :
--       JetBound (fun v : Coordinates N × Vars d => kktSystem ε (S₀+S A v.1) (eta 384 A v.1) v.2)
--         (x,z) (300*(coarseBudget d N ε σ)^5)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Calculus.JetBound`, `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.invH`, `OAI.CurrentKS.Hermitian.pd`, `OAI.CurrentKS.State.Coordinates`, `OAI.CurrentKS.State.S`, `OAI.CurrentKS.State.coarseBudget`, `OAI.CurrentKS.State.eta`, `OAI.CurrentKS.Variational.PairHilbert`, `OAI.CurrentKS.Variational.Vars`, `OAI.CurrentKS.Variational.kktSystem`, `OAI.CurrentKS.Variational.mCoord`, `OAI.CurrentKS.Variational.nCoord`, `OAI.CurrentKS.Variational.xCoord`, `OAI.CurrentKS.Variational.yCoord` and `OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.State.instNormedAddCommGroupVars` and `OAI.CurrentKS.State.instNormedSpaceRealVars` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.value_strip_derivatives` of this split imports it.
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

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupVars
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealVars
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceVars
attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
lemma kkt_strip_jet (A : Fin N → H d) (hA : ∀ i,‖A i‖ ≤ 1)
    (S₀ : H d) (hS₀ : ‖S₀‖ ≤ (d:ℝ)+1) (x : Coordinates N) {ε σ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ/2)
    (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (hz : ‖z‖ ≤ 200+(200/ε)*((d:ℝ)+1))
    (hiX : ‖invH (xCoord d z)‖ ≤ 200*((d:ℝ)+1))
    (hiY : ‖invH (yCoord d z)‖ ≤ 200*((d:ℝ)+1))
    (hP : ‖mCoord d z‖ ≤ 1) (hQ : ‖nCoord d z‖ ≤ 1) :
    JetBound (fun v : Coordinates N × Vars d => kktSystem ε (S₀+S A v.1) (eta 384 A v.1) v.2)
      (x,z) (300*(coarseBudget d N ε σ)^5) := by
  sorry

end
end CurrentKS.State

end OAI
end
