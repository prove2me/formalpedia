-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Test_mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous
-- name    : LIDT.MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T17:56:38.792274+00:00
-- url     : https://prove2.me/theorems/b19b502f-b36d-410f-99c2-a5304dbb0c0d
-- title:
--   Main Formal Step5 Self Consistency Of Expansion Bound Heterogeneous
-- statement:
--   **Evaluated polynomial consistency yields constant-family consistency with the collision loss.**
--
--   Let `Left` and `Right` be polynomial submeasurements on possibly different registers, let the state be normalized, and assume their evaluation families are consistent over uniformly sampled points with error `zeta`. Then their constant families are consistent over `Unit` with error
--
--   $$
--   \zeta+\frac{md}{q}.
--   $$
--
--   This is the heterogeneous Step 5 packaging used by the main theorem. The additive `md/q` term is the polynomial collision mass supplied by the preceding expansion bound.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/SchwartzZippelStep.lean#L282-L313

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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

open LIDT
/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

open LIDT.MIPStarRE.LDT.Test

theorem LIDT.MIPStarRE.LDT.Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : _root_.LIDT.MIPStarRE.LDT.Parameters) [_root_.LIDT.MIPStarRE.LDT.FieldModel params.q]
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState (ιA × ιB)) (hnorm : ψ.IsNormalized)
    (Left : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιA) (Right : _root_.LIDT.MIPStarRE.LDT.SubMeas (_root_.LIDT.MIPStarRE.LDT.Polynomial params) ιB)
    (ζ : _root_.LIDT.MIPStarRE.LDT.Error)
    (hevaluated : _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point params))
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Left)
      (_root_.LIDT.MIPStarRE.LDT.polynomialEvaluationFamily params Right) ζ) :
    _root_.LIDT.MIPStarRE.LDT.ConsRel ψ (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
      (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Left) (_root_.LIDT.MIPStarRE.LDT.constSubMeasFamily Right)
      (ζ + (params.m * params.d : _root_.LIDT.MIPStarRE.LDT.Error) / params.q) := by sorry
