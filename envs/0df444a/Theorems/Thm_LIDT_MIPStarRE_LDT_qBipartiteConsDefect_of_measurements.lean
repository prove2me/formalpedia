-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_qBipartiteConsDefect_of_measurements
-- name    : LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:00:58.336115+00:00
-- url     : https://prove2.me/theorems/e8272927-73a5-4779-a5ad-2e11e7b94fd7
-- title:
--   Q Bipartite Cons Defect Of Measurements
-- statement:
--   **For complete measurements, the bipartite consistency defect is total expectation minus matching mass.**
--
--   Let `psi` be a quantum state on two finite local spaces, and let $A$ and $B$ be complete measurements with the same finite outcome type. Completeness gives
--
--   $$
--   \operatorname{qBipartiteConsDefect}(\psi,A,B)=\operatorname{ev}_{\psi}(1)-\operatorname{qBipartiteMatchMass}(\psi,A,B).
--   $$
--
--   The product of the total operators is the identity, so the total-overlap term is the expectation of $1$. The remaining term is the matching mass from corresponding outcome effects. No normalization of `psi` is assumed, so the expectation is retained explicitly.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.qBipartiteConsDefect_of_measurements`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyRole/Algebra.lean#L98-L130

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
# Role-register algebraic identities for the low individual degree test

Role-pair projection algebra, symmetrized measurement definitions, and expectation
identities for the classical role-register symmetrized state.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

/-! ### Role-pair projection algebra -/

theorem LIDT.MIPStarRE.LDT.qBipartiteConsDefect_of_measurements {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome ιB) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas =
      _root_.LIDT.MIPStarRE.LDT.ev ψ (1 : _root_.LIDT.MIPStarRE.Quantum.Op (ιA × ιB)) -
        _root_.LIDT.MIPStarRE.LDT.qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas := by sorry
