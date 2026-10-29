-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consSubMeas
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.consSubMeas
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:09:44.136378+00:00
-- url     : https://prove2.me/theorems/708e90b7-538e-4c1c-ada6-d9ba91eee170
-- title:
--   Cons Sub Meas
-- statement:
--   **Consistency with a measurement gives the same-space submeasurement statement.**
--
--   Let `A` be an indexed submeasurement and `B` an indexed measurement on the same register and question distribution. If `ConsRel` holds between `A` and the submeasurement underlying `B` with error `gamma`, then the named `ConsSubMeasStmt` holds with the same parameters:
--
--   $$
--   \operatorname{ConsRel}(\psi,\mathcal D,A,\operatorname{toIdxSubMeas}(B),\gamma)
--   \Longrightarrow
--   \operatorname{ConsSubMeasStmt}(\psi,\mathcal D,A,B,\gamma).
--   $$
--
--   This is the same-space specialization of the consistency bridge. It packages the measurement-valued right family in the statement form expected by later scalar-chain estimates.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.consSubMeas`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean#L580-L605

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
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
# Preliminary comparison theorems: consistency-to-distance estimates

Estimates converting consistency of a submeasurement and a measurement into
state-dependent distance controls for the diagonal and total sandwich families
of `prop:cons-sub-meas`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Consistency controls for `prop:cons-sub-meas` -/

theorem LIDT.MIPStarRE.LDT.Preliminaries.consSubMeas {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ι × ι)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ι)
    (B : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ι) (γ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      A
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) γ →
    _root_.LIDT.MIPStarRE.LDT.Preliminaries.ConsSubMeasStmt ψ 𝒟 A B γ := by sorry
