-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_bipartiteSSCRel_of_consRel_self_measurement
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.bipartiteSSCRel_of_consRel_self_measurement
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:21:59.630093+00:00
-- url     : https://prove2.me/theorems/e3f0085e-13b7-4935-b66c-b6134f2a51c4
-- title:
--   Bipartite SSCRel Of Cons Rel Self Measurement
-- statement:
--   **Diagonal consistency of a full measurement implies bipartite strong self-consistency.**
--
--   Let `psi` be a quantum state on two copies of a finite index type, let `D` be a question distribution, and let `A` be an indexed full measurement with finite outcomes. If the ordinary consistency relation `ConsRel` holds for the submeasurement underlying `A` compared with itself at error `delta`, then `BipartiteSSCRel psi D A delta` holds. Completeness of the measurement makes the total-mass terms identities, so the diagonal consistency defect and the bipartite strong self-consistency defect agree question by question. The conclusion uses the same state, distribution, converted submeasurement, and error.
--
--   $$
--   \operatorname{ConsRel}(\psi,D,A,A,\delta)
--   \Longrightarrow
--   \operatorname{BipartiteSSCRel}(\psi,D,A,\delta),
--   \qquad A\text{ a full measurement}.
--   $$
--
--   This is the converse needed in the pasting arguments when the family is measurement-valued. It is specific to a complete indexed measurement; the statement does not claim this reverse implication for an arbitrary submeasurement.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.bipartiteSSCRel_of_consRel_self_measurement`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SelfConsistency/Core.lean#L246-L274

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries

open LIDT
/-!
# Self-consistency: core squared-mass bounds

Squared-mass lower bound lemma derived from bipartite self-consistency on
permutation-invariant states (`prop:cool-prop`).

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem LIDT.MIPStarRE.LDT.Preliminaries.bipartiteSSCRel_of_consRel_self_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι))
    (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ι) (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    @_root_.LIDT.MIPStarRE.LDT.ConsRel Question Outcome ι ι _ _ _ _ _ ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) δ →
      _root_.LIDT.MIPStarRE.LDT.BipartiteSSCRel ψ 𝒟 (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) δ := by sorry
