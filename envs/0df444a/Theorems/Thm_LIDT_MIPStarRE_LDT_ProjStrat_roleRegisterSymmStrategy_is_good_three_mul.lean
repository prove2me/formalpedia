-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_roleRegisterSymmStrategy_is_good_three_mul
-- name    : LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:22:56.675998+00:00
-- url     : https://prove2.me/theorems/37397792-4466-41c1-9795-f480589367da
-- title:
--   Role Register Symm Strategy Is Good Three Mul
-- statement:
--   **Role-register symmetrization preserves goodness with three-times error parameters.**
--
--   Let `strategy` be a two-space projective strategy and assume it passes the full low individual degree test with error `eps`. Then its heterogeneous role-register symmetrization is good with all three parameters equal to `3 * eps`:
--
--   $$
--   \operatorname{IsGood}\bigl(\mathrm{roleRegisterSymmStrategy}(\mathrm{strategy}),
--   3\varepsilon,3\varepsilon,3\varepsilon\bigr).
--   $$
--
--   Here `IsGood` means that the symmetrized axis-parallel failure, self-consistency failure, and diagonal-line failure are respectively bounded by the three displayed parameters. The proof identifies the axis and diagonal branches with the corresponding role averages, identifies the self-consistency branch with the original point-agreement failure, and uses nonnegativity plus the original test's three-term average bound to bound each component by `3 * eps`. The only premise is the stated low individual degree test pass condition.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyBiProjRoleAverage/Final.lean#L133-L169

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
# Role-Register Averaging: Goodness Bound

This module packages the branch equalities into the three-times-error goodness
bound for the role-register symmetric strategy.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open MIPStarRE.Quantum

open LIDT.MIPStarRE.LDT.ProjStrat

theorem LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmStrategy_is_good_three_mul
    {params : _root_.LIDT.MIPStarRE.LDT.Parameters} [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    {strategy : _root_.LIDT.MIPStarRE.LDT.ProjStrat params ιA ιB} {eps : _root_.LIDT.MIPStarRE.LDT.Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    (strategy.roleRegisterSymmStrategy).IsGood (3 * eps) (3 * eps) (3 * eps) := by sorry
