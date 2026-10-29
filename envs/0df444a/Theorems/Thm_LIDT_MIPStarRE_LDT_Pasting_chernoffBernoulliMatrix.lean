-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_chernoffBernoulliMatrix
-- name    : LIDT.MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T16:01:33.92745+00:00
-- url     : https://prove2.me/theorems/5a37b02d-44f8-43b2-8c7f-2d8113cd48f9
-- title:
--   Chernoff Bernoulli Matrix
-- statement:
--   **Matrix Chernoff comparison for a Bernoulli tail.** Let $\psi$ be a normalized quantum state on a finite index space, let $0<\theta<1$, let `k` and `degree` be natural numbers, and let $X$ be a positive semidefinite operator with $X\le I$. Write $d_0$ for `degree`, and assume
--
--   $$
--   \frac{2d_0}{\theta}\le k.
--   $$
--
--   Assume that the one-outcome submeasurement whose sole effect and total operator are both $X$ is complete in state $\psi$ with lower bound $1-\kappa$. Let $\mathcal T$ denote the Bernoulli-tail submeasurement built from $X$ using `k` and `degree`. Then
--
--   $$
--   \operatorname{CompletenessAtLeast}\!\left(\psi,\mathcal T,
--   1-\frac{\kappa}{1-\theta}-\exp\!\left(-\frac{\theta^2 k}{2}\right)\right).
--   $$
--
--   The tail retains the binomial terms of degrees `degree + 1` through `k`. This is the operator-level reduction of the scalar Bernoulli tail estimate through continuous functional calculus, used in the completeness and nontriviality parts of the pasting argument.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Bernoulli/MatrixChernoff.lean#L75-L154

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
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
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT.MIPStarRE.LDT.Pasting
end LIDT.MIPStarRE.LDT.Pasting

open LIDT
/-!
# Section 12 pasting: matrix Chernoff comparison

Continuous-functional-calculus form of the Bernoulli matrix Chernoff lemma.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma LIDT.MIPStarRE.LDT.Pasting.chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι)
    (hnorm : ψ.IsNormalized)
    (theta : _root_.LIDT.MIPStarRE.LDT.Error) (k degree : ℕ) (X : _root_.LIDT.MIPStarRE.Quantum.Op ι) (kappa : _root_.LIDT.MIPStarRE.LDT.Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : _root_.LIDT.MIPStarRE.LDT.Error)) / theta ≤ (k : _root_.LIDT.MIPStarRE.LDT.Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : _root_.LIDT.MIPStarRE.LDT.CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := fun _ => hXpsd
         sum_eq_total := Fintype.sum_unique fun _ => X
         total_le_one := hXleOne } : _root_.LIDT.MIPStarRE.LDT.SubMeas Unit ι)
      (1 - kappa)) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by sorry
