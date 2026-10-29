-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_simeqToApprox_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:40.821011+00:00
-- url     : https://prove2.me/theorems/c26f37aa-a2f5-4427-ab56-d4f850444415
-- title:
--   Simeq To Approx Heterogeneous
-- statement:
--   **Heterogeneous consistency of measurements implies a bipartite SDD relation.**
--
--   Let `A` and `B` be indexed measurements with the same question and outcome sets, possibly acting on different registers of the bipartite state $\psi$. If the underlying indexed submeasurements satisfy heterogeneous `ConsRel` with error $\delta$, then placing the two measurement families on the left and right registers gives `SDDRel` with error $2\delta$:
--
--   $$
--   \operatorname{ConsRel}\left(\psi,\mathcal D,
--     \operatorname{toIdxSubMeas}(A),\operatorname{toIdxSubMeas}(B),\delta\right)
--   \Longrightarrow
--   \operatorname{SDDRel}\left(\psi,\mathcal D,
--     \operatorname{placeLeft}(\operatorname{toIdxSubMeas}(A)),
--     \operatorname{placeRight}(\operatorname{toIdxSubMeas}(B)),
--     2\delta\right).
--   $$
--
--   This is the heterogeneous consistency-to-approximation bridge. The only numerical loss is the factor two from converting the consistency defect into the placed operator squared-distance bound.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean#L199-L250

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

open LIDT
/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder


open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

theorem LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A)
        (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) δ →
      _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
        (2 * δ) := by sorry
