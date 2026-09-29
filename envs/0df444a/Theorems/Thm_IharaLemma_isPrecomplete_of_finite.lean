-- Prove2me | Theorems.Thm_IharaLemma_isPrecomplete_of_finite
-- name    : IharaLemma.isPrecomplete_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/15e001f5-6cdf-59be-92b8-2527a09b53ce
-- title:
--   Finite modules over an I-adically precomplete ring are precomplete
-- statement:
--   Let $R$ be a commutative ring and $I \subseteq R$ an ideal such that $R$ is $I$-adically precomplete, in Mathlib's sense: every sequence $(r_n)_{n \in \mathbb{N}}$ in $R$ that is Cauchy for the $I$-adic filtration (that is, $r_m \equiv r_n$ modulo $I^m$ whenever $m \le n$) admits a limit, i.e. an element $r \in R$ with $r_n \equiv r$ modulo $I^n$ for every $n$. Let $M$ be an $R$-module which is finite, i.e. finitely generated over $R$. The conclusion is that $M$ is then $I$-adically precomplete as well: for every sequence $(m_n)_{n \in \mathbb{N}}$ in $M$ with $m_j \equiv m_n$ modulo $I^j \cdot M$ whenever $j \le n$, there exists $m \in M$ such that $m_n \equiv m$ modulo $I^n \cdot M$ for all $n$. No separatedness or Hausdorff hypothesis is imposed, and no Noetherian hypothesis on $R$ is needed; only precompleteness of the base ring and finite generation of the module.
--
--   This is the standard statement that precompleteness of the $I$-adic filtration passes from a ring to its finitely generated modules, the precomplete half of the classical fact that the $I$-adic completion of a finite module over a complete ring is the base change of the module to the completion. It is used in this development to produce idempotent splittings, via [`IharaLemma.nonempty_idempotentSplitting_of_finite`](thm.html#IharaLemma.nonempty_idempotentSplitting_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_isPrecomplete_of_finite.lean

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by sorry
