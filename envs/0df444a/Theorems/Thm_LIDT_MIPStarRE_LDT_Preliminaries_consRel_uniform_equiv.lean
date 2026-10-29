-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consRel_uniform_equiv
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:38.532395+00:00
-- url     : https://prove2.me/theorems/5ea714ec-8248-4d59-822f-81534ad8bd32
-- title:
--   Cons Rel Uniform Equiv
-- statement:
--   **Uniform consistency is invariant under reindexing by an equivalence.**
--
--   Let `e : alpha equiv beta`, and let `A` and `B` be indexed submeasurements on `alpha`. Their uniform consistency relation is equivalent to the relation on `beta` obtained by pulling questions back along `e.symm`:
--
--   $$
--   \operatorname{ConsRel}(\psi,\operatorname{Unif}(\alpha),A,B,\delta)
--   \Longleftrightarrow
--   \operatorname{ConsRel}(\psi,\operatorname{Unif}(\beta),A\circ e^{-1},B\circ e^{-1},\delta).
--   $$
--
--   The error is unchanged because finite uniform distributions are transported exactly by an equivalence. This utility supports the many tuple and endpoint reindexings in the induction and pasting arguments.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean#L582-L626

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
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

open LIDT
/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder


open LIDT.MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_equiv
    {α β Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (e : α ≃ β)
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas α Outcome ιA)
    (B : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas α Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) A B δ ↔
      _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution β)
        (fun b => A (e.symm b))
        (fun b => B (e.symm b))
        δ := by sorry
