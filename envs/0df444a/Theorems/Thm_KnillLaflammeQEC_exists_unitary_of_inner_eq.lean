-- Prove2me | Theorems.Thm_KnillLaflammeQEC_exists_unitary_of_inner_eq
-- name    : KnillLaflammeQEC.exists_unitary_of_inner_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:08.752982+00:00
-- url     : https://prove2.me/theorems/08525c23-c856-4f95-b8be-53b8c30d8952
-- title:
--   Proof of Theorem 3.2, p.15, [23] — families with equal inner products are related by a unitary
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space and $\{v_a\}_{a\in\beta}$, $\{w_a\}_{a\in\beta}$ two families of vectors of $\mathcal H$ indexed by the same arbitrary set $\beta$, with identical inner-product relationships:
--
--   $$
--   \langle v_a|v_b\rangle=\langle w_a|w_b\rangle\qquad\text{for all }a,b\in\beta.
--   $$
--
--   Then there is a unitary operator $U$ on $\mathcal H$ with $Uv_a=w_a$ for every $a$.
--
--   In the proof of Theorem 3.2 Knill and Laflamme apply this (citing [23]) to $v_a=A_a|0_L\rangle$ and $w_a=A_a|i_L\rangle$, whose inner products agree by condition (19), to obtain the unitaries $U_i$ with $U_iA_a|0_L\rangle=A_a|i_L\rangle$.
--
--   Differences from the source:
--   - encoding: an $n$-dimensional Hilbert space $\mathcal H$ and linear operators on it → `EuclideanSpace ℂ ι` for a finite type `ι`, operators `Matrix ι ι ℂ` acting by `QAlgorithms.act`; reason: Lean convention; every $n$-dimensional Hilbert space is isometric to $\mathbb C^n$, so the instances are the same
--   - generalization: unitaries $U_i$ with $U_iA_a|0_L\rangle=A_a|i_L\rangle$ for all $A_a$, from the identical inner-product relationships between the $A_a|0_L\rangle$ and the $A_a|i_L\rangle$ [23] → any two families `v w : β → H` with equal inner products are related by a unitary `U ∈ Matrix.unitaryGroup ι ℂ`; reason: this is the general fact the paper cites from [23]; taking $v_a=A_a|0_L\rangle$, $w_a=A_a|i_L\rangle$ gives the paper's claim
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, proof of Theorem 3.2, pp.14–15, citing [23]

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
proof of Theorem 3.2, pp.14–15, citing [23]: "The existence of unitary operators satisfying the
second condition follows from Eq.(19), according to which the innerproduct relationships between
the `A_a|0_L⟩` and the `A_a|i_L⟩` are identical [23]." Stated as the general fact used: two
families of vectors of a finite-dimensional Hilbert space with the same inner products
`⟨v_a|v_b⟩ = ⟨w_a|w_b⟩` are related by a unitary, `U v_a = w_a`.

**Formalization Note.** `H = EuclideanSpace ℂ ι`, unitaries are elements of
`Matrix.unitaryGroup ι ℂ` acting by `QAlgorithms.act`. The families are indexed by an
arbitrary type `β` (the paper's index `a` of the interaction operators, possibly infinite). -/
theorem exists_unitary_of_inner_eq {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (v w : β → EuclideanSpace ℂ ι) (h : ∀ a b, inner ℂ (v a) (v b) = inner ℂ (w a) (w b)) :
    ∃ U ∈ Matrix.unitaryGroup ι ℂ, ∀ a, QAlgorithms.act U (v a) = w a := by sorry

end KnillLaflammeQEC
