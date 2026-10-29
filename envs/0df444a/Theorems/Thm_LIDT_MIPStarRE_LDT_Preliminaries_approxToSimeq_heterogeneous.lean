-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_approxToSimeq_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:09:47.764662+00:00
-- url     : https://prove2.me/theorems/b4217410-b5f3-40f6-b790-f16dee09b3a1
-- title:
--   Approx To Simeq Heterogeneous
-- statement:
--   **A heterogeneous projective SDD relation implies consistency with the original error.**
--
--   Let `A` and `B` be indexed projective measurements on possibly different registers. If their placed left-right operator families satisfy `SDDRel` with error `2 delta`, then the underlying indexed submeasurements satisfy heterogeneous `ConsRel` with error `delta`:
--
--   $$
--   \operatorname{SDDRel}(\psi,\mathcal D,\operatorname{placeLeft}(A),\operatorname{placeRight}(B),2\delta)
--   \Longrightarrow
--   \operatorname{ConsRel}(\psi,\mathcal D,A,B,\delta).
--   $$
--
--   Projectivity supplies the converse bridge from operator-distance control to the consistency quantity. This theorem is used where projective polynomial measurements must be returned to the paper's consistency formulation.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/ComparisonProjective.lean#L334-L378

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
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
# Preliminary comparison theorems: projective converse

Projective-case converse of `prop:simeq-to-approx`. This lemma lives in a
sibling module to `ComparisonCore` because its proof uses
`projSubMeas_diagMass_eq_mass`, which is introduced in
`SwitchSandwichPrep.Core`, downstream of `ComparisonCore`.

The imports above are chosen to make the direct dependencies explicit rather
than relying on transitive re-exports through `SwitchSandwichPrep.Core`:
`ComparisonCore` is the sibling comparison module, `ConsistencyBridges`
supplies the `BipartiteSDDRel`/`ConsRel` bridging machinery, and
`SwitchSandwichPrep.Core` provides `projSubMeas_diagMass_eq_mass`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT





-- The heterogeneous proof expands the projective identity on the tensor-product
-- space; the final algebra is the same as the same-space theorem above, but the
-- generated matrix expressions are larger.

theorem LIDT.MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (𝒟 : _root_.LIDT.MIPStarRE.LDT.Distribution Question)
    (A : _root_.LIDT.MIPStarRE.LDT.IdxProjMeas Question Outcome ιA) (B : _root_.LIDT.MIPStarRE.LDT.IdxProjMeas Question Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.SDDRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeLeft (ιB := ιB) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A))
        (_root_.LIDT.MIPStarRE.LDT.IdxSubMeas.placeRight (ιA := ιA) (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B))
        (2 * δ) →
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ 𝒟
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas A)
        (_root_.LIDT.MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas B) δ := by sorry
