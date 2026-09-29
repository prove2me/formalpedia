-- Prove2me | Theorems.Thm_ModularForm_coeffHeckeU_comm
-- name    : ModularForm.coeffHeckeU_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/5775d3a4-e629-5eee-a4a1-1d422c2910f2
-- title:
--   Commutativity of the coefficient operators Uₚ and U_q
-- statement:
--   For natural numbers $p$ and $q$ and an arbitrary function $a : \mathbb{N} \to \mathbb{C}$ (a formal sequence of Fourier coefficients, with no modularity, growth or multiplicativity assumption), the two iterated applications of the coefficient-level operator [`ModularForm.coeffHeckeU`](def/ModularForm_HeckeOperator.html#L165) agree: $$\mathrm{coeffHeckeU}\,p\,(\mathrm{coeffHeckeU}\,q\,a) = \mathrm{coeffHeckeU}\,q\,(\mathrm{coeffHeckeU}\,p\,a),$$ an equality of functions $\mathbb{N} \to \mathbb{C}$. Here [`ModularForm.coeffHeckeU p a`](def/ModularForm_HeckeOperator.html#L165) is by definition the sequence $n \mapsto a(n p)$, that is, the reindexing of $a$ along multiplication by $p$; thus the left-hand side sends $n$ to $a(n p q)$ and the right-hand side sends $n$ to $a(n q p)$. No primality of $p$ or $q$, and no coprimality of $p$ and $q$, is assumed: the identity is unconditional in the two natural-number parameters, and in particular holds for $p = q$ and when either is $0$ or $1$.
--
--   This is the coefficient-sequence shadow of the classical commutation $U_p U_q = U_q U_p$ for the Hecke operators $U$ attached to two integers, formulated purely in terms of the action $a(n) \mapsto a(np)$ on Fourier expansions. It is used to establish the corresponding commutation of the operators on spaces of modular forms ([`ModularFormClass.heckeU_heckeU_comm`](thm.html#ModularFormClass.heckeU_heckeU_comm)) and, through that, in the construction of normalised eigenforms ([`CuspForm.exists_isNormalizedEigenform`](thm.html#CuspForm.exists_isNormalizedEigenform)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_coeffHeckeU_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.coeffHeckeU_comm (p q : ℕ) (a : ℕ → ℂ) : ModularForm.coeffHeckeU p (ModularForm.coeffHeckeU q a) = ModularForm.coeffHeckeU q (ModularForm.coeffHeckeU p a) := by sorry
