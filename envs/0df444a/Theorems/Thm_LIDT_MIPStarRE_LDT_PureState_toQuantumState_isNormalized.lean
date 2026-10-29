-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_toQuantumState_isNormalized
-- name    : LIDT.MIPStarRE.LDT.PureState.toQuantumState_isNormalized
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:07.47+00:00
-- url     : https://prove2.me/theorems/a8a2ce70-c60e-404a-918b-a9373542a3ea
-- title:
--   To Quantum State Is Normalized
-- statement:
--   **A pure-state density operator is normalized.** Let $\iota$ be a finite nonempty index set and let $\psi$ be a pure state with unit vector $v_\psi$. Write $\rho_\psi$ for its associated quantum state. Then
--
--   $$
--   \operatorname{IsNormalized}(\rho_\psi).
--   $$
--
--   Thus the rank-one density construction satisfies the normalized-trace condition required by the quantum-state expectation API.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.PureState.toQuantumState_isNormalized`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/QuantumState.lean#L124-L127

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













open LIDT.MIPStarRE.LDT.PureState

theorem LIDT.MIPStarRE.LDT.PureState.toQuantumState_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.PureState ι) :
    (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι).IsNormalized := by sorry
