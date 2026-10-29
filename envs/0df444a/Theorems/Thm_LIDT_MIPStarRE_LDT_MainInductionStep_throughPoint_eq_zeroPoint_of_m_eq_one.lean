-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_throughPoint_eq_zeroPoint_of_m_eq_one
-- name    : LIDT.MIPStarRE.LDT.MainInductionStep.throughPoint_eq_zeroPoint_of_m_eq_one
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T14:34:12.665236+00:00
-- url     : https://prove2.me/theorems/806b4c22-9b09-4d94-a62c-befb3f5cd629
-- title:
--   Through Point Eq Zero Point Of M Eq One
-- statement:
--   **At one ambient coordinate, every axis-parallel line has the same representative.**
--
--   Let $(q,m,d)$ have a field model and assume $m=1$. For any point $u\in\mathbb{F}_q^m$ and coordinate index $i\in\mathrm{Fin}(m)$, the canonical axis-parallel line through $u$ in direction $i$ is the same as the line through the zero point:
--
--   $$
--   \operatorname{throughPoint}(u,i)=\operatorname{throughPoint}(0,i).
--   $$
--
--   When there is only one coordinate, changing the base point does not change the underlying affine line. This geometric fact is used in the base case of the main induction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.MainInductionStep.throughPoint_eq_zeroPoint_of_m_eq_one`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/InductionParameterBounds/Preliminaries.lean#L29-L49

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
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open LIDT
/-!
# Section 6 — Induction Parameter Bound Preliminaries

This file is one leaf of `InductionParameterBounds`. It contains the elementary
point-line reduction for the base case, the real-variable comparison lemmas used
by the small-parameter estimates, and the bound `d/q ≤ 1`.

## References

- `blueprint/src/chapter/ch10_induction.tex`
- `references/ldt-paper/inductive_step.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem LIDT.MIPStarRE.LDT.MainInductionStep.throughPoint_eq_zeroPoint_of_m_eq_one
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (hm1 : params.m = 1)
    (u : _root_.LIDT.MIPStarRE.LDT.Point params) (i : Fin params.m) :
    _root_.LIDT.MIPStarRE.LDT.AxisParallelLine.throughPoint (params := params) u i =
      _root_.LIDT.MIPStarRE.LDT.AxisParallelLine.throughPoint (params := params) _root_.LIDT.MIPStarRE.LDT.zeroPoint i := by sorry
