-- Prove2me | Theorems.Thm_LIDT_MIPStarRE_LDT_PureState_ev_eq_re_inner
-- name    : LIDT.MIPStarRE.LDT.PureState.ev_eq_re_inner
-- status  : Proved
-- author  : @Dengnifer
-- created : 2026-10-27T13:41:07.69773+00:00
-- url     : https://prove2.me/theorems/dad8d7b9-d5f1-4df6-823b-96ce80ca4612
-- title:
--   Ev Eq Re Inner
-- statement:
--   **Pure-state expectation as a vector inner product.** Let $\iota$ be a finite nonempty index set, let $\psi$ be a pure state with unit vector $v_\psi$, and let $X$ be an operator on $\mathbb C^\iota$. Write $\rho_\psi$ for the quantum state associated with $\psi$. Then
--
--   $$
--   \operatorname{ev}(\rho_\psi,X)=\operatorname{Re}\!\left(\langle v_\psi,Xv_\psi\rangle\right).
--   $$
--
--   This translates the normalized-trace expectation into the usual vector calculation for a pure state.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
--
--   **Formalization Note.** The source declaration is `MIPStarRE.LDT.PureState.ev_eq_re_inner`; its Lean statement gives the exact quantifier order and all boundary hypotheses.
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/QuantumState.lean#L183-L188

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

theorem LIDT.MIPStarRE.LDT.PureState.ev_eq_re_inner {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : _root_.LIDT.MIPStarRE.LDT.PureState ι) (X : _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.LIDT.MIPStarRE.LDT.ev (ψ : _root_.LIDT.MIPStarRE.LDT.QuantumState ι) X =
      Complex.re (star ψ.vector ⬝ᵥ (X *ᵥ ψ.vector)) := by sorry
