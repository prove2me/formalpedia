-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_Pasting_bernoulliTailOperator_leftTensor
-- name    : LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator_leftTensor
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T16:43:53.174761+00:00
-- url     : https://prove2.me/theorems/271be54e-f2eb-456d-a4b3-9e3f937a97d6
-- title:
--   Bernoulli Tail Operator Left Tensor
-- statement:
--   **The matrix-valued Bernoulli tail commutes with left tensor placement.** Let $A$ be a one-register operator, let `k` be a natural number, and write $d_0$ for `degree`. Define
--
--   $$
--   F_{k,d_0}(A)=\sum_{r=d_0+1}^{k}\binom{k}{r}A^r(I-A)^{k-r}.
--   $$
--
--   Then the Bernoulli-tail polynomial commutes with left placement:
--
--   $$
--   F_{k,d_0}(\operatorname{leftTensor}(A))
--   =\operatorname{leftTensor}(F_{k,d_0}(A)).
--   $$
--
--   This identity moves Bernoulli-tail operators through tensor placement in the completeness and nontriviality parts of the pasting construction.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.Pasting.bernoulliTailOperator_leftTensor`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Defs/Tuples.lean#L179-L195

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open LIDT
/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

@[expose] public section

open LIDT.MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator_leftTensor (A : _root_.LIDT.MIPStarRE.Quantum.Op ι)
    (k degree : ℕ) :
    _root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree (_root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) A) =
      _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι) (_root_.LIDT.MIPStarRE.LDT.Pasting.bernoulliTailOperator k degree A) := by sorry
