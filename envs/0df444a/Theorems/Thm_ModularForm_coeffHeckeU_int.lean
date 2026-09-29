-- Prove2me | Theorems.Thm_ModularForm_coeffHeckeU_int
-- name    : ModularForm.coeffHeckeU_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5676ad18-c8ac-521e-b502-0131dc81e7be
-- title:
--   Integrality of the coefficient operator Uₚ
-- statement:
--   Let $p$ be a natural number and let $a : \mathbb{N} \to \mathbb{C}$ be a sequence of complex numbers, subject to the hypothesis that each term is an integer: for every $n \in \mathbb{N}$ there is $m \in \mathbb{Z}$ with $a(n) = m$ (under the coercion $\mathbb{Z} \to \mathbb{C}$). Let $n \in \mathbb{N}$. The assertion is that the $n$-th term of the transformed sequence [`ModularForm.coeffHeckeU p a`](def/ModularForm_HeckeOperator.html#L165), which by definition is $a(n \cdot p)$, is again an integer: there exists $m \in \mathbb{Z}$ with [`ModularForm.coeffHeckeU p a n`](def/ModularForm_HeckeOperator.html#L165) $= m$. No primality or positivity is assumed of $p$, and no modularity or growth condition is imposed on $a$; the statement concerns only the reindexing $n \mapsto a(n \cdot p)$ of an arbitrary sequence of complex numbers, term by term at the single index $n$.
--
--   This records that the coefficient-side operator $U_p$, acting on $q$-expansion coefficient sequences by $(U_p a)_n = a_{np}$, carries sequences of integers to sequences of integers, i.e. preserves the integral lattice at the level of coefficients. It is used by [`CuspForm.mem_intLattice_of_coe_eq_heckeU`](thm.html#CuspForm.mem_intLattice_of_coe_eq_heckeU), where a cusp form whose coefficients arise in this way is placed in the lattice of forms with integral Fourier coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_coeffHeckeU_int.lean

import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.coeffHeckeU_int (p : ℕ) {a : ℕ → ℂ} (ha : ∀ n : ℕ, ∃ m : ℤ, a n = m) (n : ℕ) : ∃ m : ℤ, ModularForm.coeffHeckeU p a n = m := by sorry
