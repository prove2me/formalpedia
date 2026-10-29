-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_ProjStrat_qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average
-- name    : LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T18:17:02.578739+00:00
-- url     : https://prove2.me/theorems/ec9dcfd4-e98f-4992-8fa8-de0630807d9e
-- title:
--   Q Bipartite Cons Defect Role Register Proj Meas Arbitrary Eq Average
-- statement:
--   **Role-register consistency defect is the average of the two extracted defects.**
--
--   For a normalized state, projective measurements `M_A`,`M_B`, and an arbitrary heterogeneous role-register measurement `G`, the symmetrized bipartite consistency defect decomposes into the two occupied principal blocks:
--
--   $$
--   \operatorname{qBipartiteConsDefect}(\psi_{\mathrm{sym}},\operatorname{roleRegisterProjMeas}(M_A,M_B),G)
--   =\frac{\operatorname{qBipartiteConsDefect}(\psi,M_A,G_B)+
--   \operatorname{qBipartiteConsDefect}(\psi,G_A,M_B)}{2}.
--   $$
--
--   The match-mass identity supplies the corresponding positive terms, and normalization identifies the defect as one minus match mass. This is the questionwise identity used to unsymmetrize point consistency.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/StrategyBiProjUnsymmetrization.lean#L659-L702

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
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
# Heterogeneous role-register measurement extraction

This file contains the principal-block extraction used to unsymmetrize a
measurement on the heterogeneous role-register space
`Role × (ιA ⊕ ιB)`.  The Alice extraction is the block indexed by
`(Role.A, Sum.inl _)`; the Bob extraction is the block indexed by
`(Role.B, Sum.inr _)`.

These are the two-space analogues of the same-space extractions in
`MIPStarRE.LDT.Test.Unsymmetrization`.  They preserve POVM completeness, but
they do not assert that arbitrary principal blocks of a projective measurement
remain projective.  As in the paper proof, projectivity is restored later by
the projectivization step.

## References

* `references/ldt-paper/inductive_step.tex`, lines 84--109.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT




open LIDT.MIPStarRE.LDT.ProjStrat

/-! ### Extraction on the constructed role-register measurements -/

/-! ### Trace compression for occupied role-register sectors -/

theorem LIDT.MIPStarRE.LDT.ProjStrat.qBipartiteConsDefect_roleRegisterProjMeas_arbitrary_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome ιA) (MB : _root_.LIDT.MIPStarRE.LDT.ProjMeas Outcome ιB)
    (G : _root_.LIDT.MIPStarRE.LDT.Measurement Outcome (_root_.LIDT.MIPStarRE.LDT.ProjStrat.RoleRegisterLocal ιA ιB)) :
    _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterSymmState ψ)
        (_root_.LIDT.MIPStarRE.LDT.ProjStrat.roleRegisterProjMeas MA MB).toSubMeas G.toSubMeas =
      (_root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ MA.toSubMeas (G.extractRoleRegisterBob).toSubMeas +
        _root_.LIDT.MIPStarRE.LDT.qBipartiteConsDefect ψ (G.extractRoleRegisterAlice).toSubMeas MB.toSubMeas) / 2 := by sorry
