-- Prove2me | Theorems.Thm_OAI_CurrentKS_Variational_jetBound_kktGiven
-- name    : OAI.CurrentKS.Variational.jetBound_kktGiven
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:33.216224+00:00
-- url     : https://prove2.me/theorems/ef2694c4-effa-45ff-b325-fcd0076c30c5
-- title:
--   OAI.CurrentKS.Variational.jetBound_kktGiven: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.Variational`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Calculus Matrix`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius`):
--
--   ```lean
--   lemma jetBound_kktGiven (Z : E →L[ℝ] Vars d) {S : E → H d}
--       {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
--       (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (hε : |ε| ≤ B)
--       (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
--       (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
--       (hM : ‖mCoord d (Z z)‖ ≤ 1) (hN : ‖nCoord d (Z z)‖ ≤ 1)
--       (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
--       (hSB : JetBound S z B) (hηB : JetBound η z B) :
--       JetBound (fun v => kktSystem ε (S v) (η v) (Z v)) z (300*B^5)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Calculus.JetBound`, `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.invH`, `OAI.CurrentKS.Hermitian.pd`, `OAI.CurrentKS.Variational.PairHilbert`, `OAI.CurrentKS.Variational.Vars`, `OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1`, `OAI.CurrentKS.Variational.instNormedAddCommGroupVars_2`, `OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_1`, `OAI.CurrentKS.Variational.instNormedSpaceRealVars_2`, `OAI.CurrentKS.Variational.kktSystem`, `OAI.CurrentKS.Variational.mCoord`, `OAI.CurrentKS.Variational.nCoord`, `OAI.CurrentKS.Variational.xCoord`, `OAI.CurrentKS.Variational.yCoord`, `OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH`, `OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH` and `OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT002` of this split); `OAI.CurrentKS.Variational.instTopologicalSpaceVars` (definitions bundle `OAIQ241TT006` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.kkt_strip_jet` of this split imports it.
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
open CurrentKS.Hermitian CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdSubtypeMatMemSubmoduleRealH
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p0
local instance instNormedAddCommGroupContinuousLinearMapRealIdVars_rb5a0cf_1 : NormedAddCommGroup (E →L[ℝ] Vars d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdVars_rb5a0cf_1 : NormedSpace ℝ (E →L[ℝ] Vars d) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_2_rb5a0cf_1 : NormedAddCommGroup (E →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_2_rb5a0cf_1 : NormedSpace ℝ (E →L[ℝ] H d) := inferInstance
lemma jetBound_kktGiven (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (hM : ‖mCoord d (Z z)‖ ≤ 1) (hN : ‖nCoord d (Z z)‖ ≤ 1)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => kktSystem ε (S v) (η v) (Z v)) z (300*B^5) := by
  sorry
end
end CurrentKS.Variational

end OAI
end
