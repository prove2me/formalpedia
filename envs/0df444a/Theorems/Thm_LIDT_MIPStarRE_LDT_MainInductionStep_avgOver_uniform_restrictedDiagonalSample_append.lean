-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_MainInductionStep_avgOver_uniform_restrictedDiagonalSample_append
-- name    : LIDT.MIPStarRE.LDT.MainInductionStep.avgOver_uniform_restrictedDiagonalSample_append
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T14:48:17.799387+00:00
-- url     : https://prove2.me/theorems/dba61243-306e-4f0b-a3f8-dd6a63e84722
-- title:
--   Avg Over Uniform Restricted Diagonal Sample Append
-- statement:
--   **Uniform averaging for appended restricted diagonal samples.** Let $j$ be a predecessor coordinate direction and let $g$ be an error-valued function on successor restricted diagonal samples in the direction obtained by embedding $j$. Write a restricted predecessor sample as $(u,c)$, let $J(u,x)$ denote `appendPoint`, and let $\mathcal U$ be the uniform distribution on a slice height and such a predecessor sample. Let $\mathcal V$ be the uniform distribution on the corresponding successor restricted diagonal samples. Then
--
--   $$
--   \mathbb E_{(x,(u,c))\sim\mathcal U} g(J(u,x),c)
--   =\mathbb E_{t\sim\mathcal V} g(t).
--   $$
--
--   The statement views the restricted sample as a point paired with its free initial direction coordinates and applies `avgOver_uniform_pointAppend_prod`. It is used in both the ordinary and answer-valued weighted diagonal bounds to reindex the slice average.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.MainInductionStep.avgOver_uniform_restrictedDiagonalSample_append`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MainInductionStep/Theorems/RestrictedProbabilities/Base.lean#L67-L91

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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Lean.Elab.Tactic
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open LIDT
/-!
# Section 6 -- Restricted Probability Common Lemmas

This module contains the averaging and scalar normalization lemmas shared by the
axis-parallel, diagonal, and answer-valued restricted-probability bounds.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LIDT.MIPStarRE.LDT.MainInductionStep.avgOver_uniform_restrictedDiagonalSample_append
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters)
    [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (j : Fin params.m)
    (g : _root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next (_root_.LIDT.MIPStarRE.LDT.embedCoord params j) → _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Fq params × _root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params j))
        (fun xs => g (_root_.LIDT.MIPStarRE.LDT.appendPoint params xs.2.1 xs.1, xs.2.2)) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution
        (_root_.LIDT.MIPStarRE.LDT.RestrictedDiagonalSample params.next (_root_.LIDT.MIPStarRE.LDT.embedCoord params j))) g := by sorry
