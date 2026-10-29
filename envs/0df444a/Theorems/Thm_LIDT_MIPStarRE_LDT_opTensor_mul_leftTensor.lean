-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_opTensor_mul_leftTensor
-- name    : LIDT.MIPStarRE.LDT.opTensor_mul_leftTensor
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:33.736377+00:00
-- url     : https://prove2.me/theorems/76668951-bf5a-4a04-a899-88fc4c4b3f9e
-- title:
--   Op Tensor Mul Left Tensor
-- statement:
--   **Multiplication of a full tensor by a left-placed operator.**
--
--   Let $\iota_1$ and $\iota_2$ be finite index sets, let $A,B$ be operators on the first space, and let $C$ be an operator on the second space. Multiplying the full tensor $A\otimes C$ by the left placement $B\otimes I$ changes only the first tensor factor:
--
--   $$
--   (A\otimes C)(B\otimes I_{\iota_2})=(AB)\otimes C.
--   $$
--
--   This is the Kronecker-product multiplication rule in the orientation used by the LIDT tensor-placement API. It supports the operator rearrangements in the pasting proof, including the Cauchy-Schwarz estimates for sandwiched line measurements.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.opTensor_mul_leftTensor`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/QuantumState.lean#L370-L385

import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

open LIDT
/-!
# Quantum states and tensor placement for the low individual degree test

Core quantum-state definitions together with tensor-placement operators.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

open LIDT.MIPStarRE.LDT

theorem LIDT.MIPStarRE.LDT.opTensor_mul_leftTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι₁) (C : _root_.LIDT.MIPStarRE.Quantum.Op ι₂) :
    _root_.LIDT.MIPStarRE.LDT.opTensor A C * _root_.LIDT.MIPStarRE.LDT.leftTensor (ι₂ := ι₂) B = _root_.LIDT.MIPStarRE.LDT.opTensor (A * B) C := by sorry
