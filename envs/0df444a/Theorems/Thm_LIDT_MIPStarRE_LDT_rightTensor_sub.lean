-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_rightTensor_sub
-- name    : LIDT.MIPStarRE.LDT.rightTensor_sub
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:32.231214+00:00
-- url     : https://prove2.me/theorems/babb27eb-fd17-4322-831c-80e6e0509e1b
-- title:
--   Right Tensor Sub
-- statement:
--   **Subtraction commutes with right tensor placement.**
--
--   Let $\iota_1$ and $\iota_2$ be finite index sets, and let $A$ and $B$ be operators on the second space. The difference of their right placements is the right placement of their difference:
--
--   $$
--   (I_{\iota_1}\otimes A)-(I_{\iota_1}\otimes B)
--   =I_{\iota_1}\otimes(A-B).
--   $$
--
--   This linearity identity lets state-dependent distance and defect expressions move subtraction through a bipartite embedding. It is used in the projectivization-repair estimates when an operator difference is placed on the second register.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.rightTensor_sub`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/QuantumState.lean#L492-L500

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

theorem LIDT.MIPStarRE.LDT.rightTensor_sub
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (A B : _root_.LIDT.MIPStarRE.Quantum.Op ι₂) :
    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) A - _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) B =
      _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) (A - B) := by sorry
