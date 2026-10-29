-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_triangleSub_right_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:22:06.605117+00:00
-- url     : https://prove2.me/theorems/1abaf28b-2c61-4580-96e6-c02cac6c5f9c
-- title:
--   Triangle Sub Right Heterogeneous
-- statement:
--   **A heterogeneous right-register substitution has the same square-root loss.**
--
--   Let $\psi$ be a normalized state on $\mathcal H_A\otimes\mathcal H_B$, and let $\mathcal D$ have total weight at most one. Let $A$ be an indexed submeasurement on Alice's space and let $B,D$ be indexed measurements on Bob's space. If
--
--   $$
--   A\simeq_{\delta}B
--   $$
--
--   and the right-register placements obey
--
--   $$
--   I\otimes B\approx_{\varepsilon}I\otimes D,
--   $$
--
--   then
--
--   $$
--   A\simeq_{\delta+\sqrt{\varepsilon}}D.
--   $$
--
--   No identification of Alice's and Bob's local Hilbert spaces is required. The proof places the three families on the common bipartite space and applies the right-side matching-mass estimate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/Triangles/Core.lean#L611-L711

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









/-! ### Right-register variant of `triangleSub` -/

theorem LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_right_heterogeneous
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas Question Outcome ιA)
    (B D : _root_.LIDT.MIPStarRE.LDT.IdxMeas Question Outcome ιB) (δ ε : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAB : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      A (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B) δ)
    (hBD : _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas B))
      (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D)) ε) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
      A
      (_root_.LIDT.MIPStarRE.LDT.IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) := by sorry
