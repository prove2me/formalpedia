-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_triangleSub_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:21:59.207983+00:00
-- url     : https://prove2.me/theorems/a7ac08cf-890f-4116-a74d-6b74878a4709
-- title:
--   Triangle Sub Heterogeneous
-- statement:
--   **A left-register state-dependent substitution preserves consistency.**
--
--   Let $\psi$ be a normalized bipartite state on $\mathcal H_A\otimes\mathcal H_B$, and let $\mathcal D$ be a finite-support question distribution whose total weight is at most one. Let $A$ and $B$ be indexed measurements on Alice's space, and let $C$ be an indexed submeasurement on Bob's space, all with the same finite answer set. Assume
--
--   $$
--   A\otimes I\simeq_{\delta} I\otimes C
--   $$
--
--   under $\psi$ and $\mathcal D$, and
--
--   $$
--   A\otimes I\approx_{\varepsilon}B\otimes I.
--   $$
--
--   Then
--
--   $$
--   B\otimes I\simeq_{\delta+\sqrt{\varepsilon}} I\otimes C.
--   $$
--
--   The proof keeps the right submeasurement fixed, bounds the change in diagonal matching mass by Cauchy-Schwarz, and uses that both left families are complete measurements so their total-mass terms agree.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.triangleSub_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/Triangles/Core.lean#L308-L457

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
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
# Triangle Inequalities for State-Dependent Distance: Core

This module contains the main triangle-substitution estimates for approximate
measurements.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT









/-! ### Elementary max bound -/

theorem LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_heterogeneous
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιA) (C : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ιB)
    (δ ε : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAC : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A) C δ)
    (hAB : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas A))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)) ε) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B)
      C (δ + Real.sqrt ε) := by sorry
