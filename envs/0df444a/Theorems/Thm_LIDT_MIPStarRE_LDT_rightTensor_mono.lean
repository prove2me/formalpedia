-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_rightTensor_mono
-- name    : LIDT.MIPStarRE.LDT.rightTensor_mono
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:33.608027+00:00
-- url     : https://prove2.me/theorems/b73d0cb0-9001-4601-890f-cd6ec8682af5
-- title:
--   Right Tensor Mono
-- statement:
--   **Monotonicity of right tensor placement.**
--
--   Let $\iota_1$ and $\iota_2$ be finite index sets, let $B_1$ and $B_2$ be operators on the second space, and assume $B_1\le B_2$ in the operator order. Placing these operators on the right subsystem preserves the order:
--
--   $$
--   I_{\iota_1}\otimes B_1
--   \;\le\;
--   I_{\iota_1}\otimes B_2.
--   $$
--
--   The result expresses positivity of the identity factor in the Kronecker product. It provides the order-preserving tensor rewrite needed when bounds on one party's operator are lifted to a bipartite space.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.rightTensor_mono`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/QuantumState.lean#L325-L330

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

theorem LIDT.MIPStarRE.LDT.rightTensor_mono
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {B₁ B₂ : _root_.LIDT.MIPStarRE.Quantum.Op ι₂} (hB : B₁ ≤ B₂) :
    _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) B₁ ≤ _root_.LIDT.MIPStarRE.LDT.rightTensor (ι₁ := ι₁) B₂ := by sorry
