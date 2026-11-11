-- Prove2me | Theorems.Thm_OAI_CurrentKS_Variational_kkt_curve_derivatives
-- name    : OAI.CurrentKS.Variational.kkt_curve_derivatives
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:58:10.239092+00:00
-- url     : https://prove2.me/theorems/e2fbd33e-dfd7-4ca4-bf45-fad7b9f98677
-- title:
--   OAI.CurrentKS.Variational.kkt_curve_derivatives: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Variational`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   lemma kkt_curve_derivatives (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
--       (b h : E) (hS : ContDiffAt ℝ 3 S b) (hη : ContDiffAt ℝ 3 η b)
--       (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
--       (J : Vars d ≃L[ℝ] Vars d)
--       (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
--         (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
--         (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u)
--       {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
--       (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
--       (hFB : JetBound (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) D)
--       (c : ℝ → Vars d) (hc : ContDiffAt ℝ 3 c 0) (hc0 : c 0=z)
--       (heq : (fun t => kktSystem ε (S (b+t • h)) (η (b+t • h)) (c t)) =ᶠ[𝓝 0] (fun _ => 0)) :
--       ‖iteratedDeriv 2 c 0‖ ≤ A*D*(1+A*D)^2 ∧
--       ‖iteratedDeriv 3 c 0‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Calculus.JetBound`, `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH`, `OAI.CurrentKS.Hermitian.matrixRealInnerProduct`, `OAI.CurrentKS.Hermitian.pd`, `OAI.CurrentKS.KKT.Variables`, `OAI.CurrentKS.KKT.jacobian`, `OAI.CurrentKS.Variational.PairHilbert`, `OAI.CurrentKS.Variational.Vars`, `OAI.CurrentKS.Variational.hessian`, `OAI.CurrentKS.Variational.identityPair`, `OAI.CurrentKS.Variational.instNormedAddCommGroupVars_3`, `OAI.CurrentKS.Variational.instNormedSpaceRealVars_3`, `OAI.CurrentKS.Variational.kktSystem`, `OAI.CurrentKS.Variational.linConstraint`, `OAI.CurrentKS.Variational.mCoord`, `OAI.CurrentKS.Variational.nCoord`, `OAI.CurrentKS.Variational.onPairHilbert`, `OAI.CurrentKS.Variational.xCoord`, `OAI.CurrentKS.Variational.yCoord`, `OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_1`, `OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH`, `OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH` and `OAI.CurrentKS.Variational.instTopologicalSpaceVars` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT006` of this split).
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

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_1
private local instance instTopologicalSpacePairHilbert_rb2429b_1 : TopologicalSpace (PairHilbert d) :=
  (inferInstance : NormedAddCommGroup (PairHilbert d)).toUniformSpace.toTopologicalSpace
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_3
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_3
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p4
lemma kkt_curve_derivatives (ε : ℝ) (S : E → H d) (η : E → H d →L[ℝ] H d)
    (b h : E) (hS : ContDiffAt ℝ 3 S b) (hη : ContDiffAt ℝ 3 η b)
    (z : Vars d) (hX : xCoord d z ∈ pd d) (hY : yCoord d z ∈ pd d)
    (J : Vars d ≃L[ℝ] Vars d)
    (hJ : ∀ u,J u=CurrentKS.KKT.jacobian (identityPair d)
      (onPairHilbert (linConstraint (xCoord d z) (yCoord d z) (η b)))
      (hessian (xCoord d z) (yCoord d z) (mCoord d z) (nCoord d z)) u)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hJinv : ‖J.symm.toContinuousLinearMap‖ ≤ A) (hh : ‖h‖ ≤ 1)
    (hFB : JetBound (fun v : E × Vars d => kktSystem ε (S v.1) (η v.1) v.2) (b,z) D)
    (c : ℝ → Vars d) (hc : ContDiffAt ℝ 3 c 0) (hc0 : c 0=z)
    (heq : (fun t => kktSystem ε (S (b+t • h)) (η (b+t • h)) (c t)) =ᶠ[𝓝 0] (fun _ => 0)) :
    ‖iteratedDeriv 2 c 0‖ ≤ A*D*(1+A*D)^2 ∧
    ‖iteratedDeriv 3 c 0‖ ≤ A*D*((1+A*D)^3+3*(1+A*D)*(A*D*(1+A*D)^2)) := by
  sorry

end
end CurrentKS.Variational

end OAI
end
