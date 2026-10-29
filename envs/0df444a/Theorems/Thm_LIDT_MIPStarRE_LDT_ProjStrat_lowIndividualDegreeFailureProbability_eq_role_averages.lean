-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_lowIndividualDegreeFailureProbability_eq_role_averages
-- name    : LIDT.MIPStarRE.LDT.ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:52:09.159303+00:00
-- url     : https://prove2.me/theorems/cf461b1d-3090-41bb-9c97-82950801c6c1
-- title:
--   Low Individual Degree Failure Probability Eq Role Averages
-- statement:
--   **The low-degree failure probability is the average of the three role-register averages.**
--
--   For every two-space projective strategy, the direct low-individual-degree failure probability equals the average of its axis-parallel, point-agreement, and restricted-diagonal role averages:
--
--   $$
--   \operatorname{lowIndividualDegreeFailureProbability}(\mathrm{strategy})
--   =\frac{\operatorname{axisParallelRoleAverage}(\mathrm{strategy})
--   +\operatorname{pointAgreementFailureProbability}(\mathrm{strategy})
--   +\operatorname{diagonalRoleAverage}(\mathrm{strategy})}{3}.
--   $$
--
--   This exact decomposition lets the low-degree test control the point-agreement branch and the symmetrized strategy's role averages with the correct factor of three.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyBiProj/Measurements.lean#L525-L532

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
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
# Two-Space Projective Strategies: Role-Register Measurements

This module contains the direct-sum measurement constructors and the
role-register symmetric strategy associated to a heterogeneous projective
strategy.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.Quantum

open LIDT.MIPStarRE.LDT.ProjStrat

/-! ### Complete block-measurement constructors -/































variable {params : Parameters} [FieldModel params.q]
variable {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
variable {ιB : Type*} [Fintype ιB] [DecidableEq ιB]

/-! ### Heterogeneous role-register measurement families -/













/-! ### Paper test branches for two-space strategies -/

theorem LIDT.MIPStarRE.LDT.ProjStrat.lowIndividualDegreeFailureProbability_eq_role_averages
    (strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB) :
    strategy.lowIndividualDegreeFailureProbability =
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 := by sorry
