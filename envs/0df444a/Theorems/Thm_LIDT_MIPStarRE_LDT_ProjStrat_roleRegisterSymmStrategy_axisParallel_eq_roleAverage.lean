-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_roleRegisterSymmStrategy_axisParallel_eq_roleAverage
-- name    : LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:09:47.646901+00:00
-- url     : https://prove2.me/theorems/a17195cd-9ce6-41d7-9508-4ad3e9ee6a0f
-- title:
--   Role Register Symm Strategy Axis Parallel Eq Role Average
-- statement:
--   **The symmetrized axis-parallel failure is the original role average.**
--
--   For a two-space projective strategy with finite local spaces and the required field model, the axis-parallel failure probability of its heterogeneous role-register symmetrization is exactly the original strategy's `axisParallelRoleAverage`:
--
--   $$
--   (\mathrm{roleRegisterSymmStrategy}(\mathrm{strategy})).\mathrm{axisParallelFailureProbability}
--   =\mathrm{strategy}.\mathrm{axisParallelRoleAverage}.
--   $$
--
--   The right-hand side averages the two axis-parallel consistency experiments: Alice receives the sampled line while Bob receives its base point, and the reversed point-line assignment. Both are averaged over uniform axis-parallel test samples. The theorem is an exact identity for every supplied strategy, with no pass or error hypothesis. Its role is to replace the symmetrized branch by the role-average quantity when proving the goodness bounds for the role-register construction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Core.lean#L704-L756

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.ProjStrat
end LIDT.MIPStarRE.LDT.ProjStrat

open LIDT
/-!
# Role-Register Averaging: Branch Equalities

This module proves the role-register branch equalities for heterogeneous
projective strategies.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.Quantum

open LIDT.MIPStarRE.LDT.ProjStrat

theorem LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_axisParallel_eq_roleAverage
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB) :
    (strategy.roleRegisterSymmStrategy).axisParallelFailureProbability =
      strategy.axisParallelRoleAverage := by sorry
