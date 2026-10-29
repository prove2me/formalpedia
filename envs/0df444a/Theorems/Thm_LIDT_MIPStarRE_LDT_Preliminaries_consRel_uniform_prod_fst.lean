-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Preliminaries_consRel_uniform_prod_fst
-- name    : LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_prod_fst
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:06:35.025293+00:00
-- url     : https://prove2.me/theorems/966ba062-7b98-4b2f-a1df-622c52859ddc
-- title:
--   Cons Rel Uniform Prod Fst
-- statement:
--   **A first-coordinate uniform consistency relation lifts to a product question space.**
--
--   Let `A` and `B` be indexed submeasurements on a question type `alpha`. If they satisfy `ConsRel` with error `delta` under the uniform distribution on `alpha`, then the families that ignore the second coordinate satisfy the same relation under the uniform distribution on `alpha x beta`:
--
--   $$
--   \operatorname{ConsRel}(\psi,\operatorname{Unif}(\alpha),A,B,\delta)
--   \Longrightarrow
--   \operatorname{ConsRel}(\psi,\operatorname{Unif}(\alpha\times\beta),
--   \lambda(a,b).A(a),\lambda(a,b).B(a),\delta).
--   $$
--
--   Uniform averaging over the independent extra coordinate leaves an expression depending only on the first coordinate unchanged. This is used when lifting endpoint consistency to product-shaped questions.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Preliminaries.consRel_uniform_prod_fst`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean#L550-L580

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

lemma LIDT.MIPStarRE.LDT.Preliminaries.consRel_uniform_prod_fst
    {α β Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB))
    (A : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas α Outcome ιA)
    (B : _root_.LIDT.MIPStarRE.LDT.IdxSubMeas α Outcome ιB)
    (δ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hAB : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution α) A B δ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (α × β))
      (fun ab => A ab.1)
      (fun ab => B ab.1)
      δ := by sorry
