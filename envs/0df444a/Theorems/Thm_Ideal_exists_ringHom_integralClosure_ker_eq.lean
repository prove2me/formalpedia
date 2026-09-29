-- Prove2me | Theorems.Thm_Ideal_exists_ringHom_integralClosure_ker_eq
-- name    : Ideal.exists_ringHom_integralClosure_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/b9ce7246-a985-5f5f-932c-e8a9bda62a8c
-- title:
--   Primes of finite ℤ-algebras as kernels of ℤ̄-valued characters
-- statement:
--   Let $T$ be a commutative ring that is finite as a $\mathbb{Z}$-module, and let $\mathfrak{P}$ be an ideal of $T$ which is prime. Assume further that $\mathfrak{P}$ meets the image of $\mathbb{Z}$ only in zero, in the sense that for every integer $n$ with $n\cdot 1_T \in \mathfrak{P}$ one has $n = 0$. The conclusion is that there exists a ring homomorphism $f \colon T \to \mathrm{integralClosure}\ \mathbb{Z}\ \mathbb{C}$, that is, a homomorphism from $T$ to the ring of algebraic integers inside $\mathbb{C}$ (the integral closure of $\mathbb{Z}$ in $\mathbb{C}$, viewed as a subring), whose kernel, as an ideal of $T$, is exactly $\mathfrak{P}$. Note that the asserted $f$ is merely a ring homomorphism, and only existence is claimed: no uniqueness, and no compatibility beyond the identification of the kernel with $\mathfrak{P}$, is asserted.
--
--   This is the commutative-algebra half of the Deligne–Serre lifting lemma: a prime of a ring finite over $\mathbb{Z}$ which contracts to $(0)$ in $\mathbb{Z}$ is the kernel of a character valued in the algebraic integers, since the quotient is an order in a number field. In the present development it is used to convert a prime of a Hecke-type algebra into a complex algebraic-integer-valued eigencharacter, and is cited by [`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`](thm.html#WeierstrassCurve.isModularModelOfLevel_of_patchingDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_ringHom_integralClosure_ker_eq.lean

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.exists_ringHom_integralClosure_ker_eq {T : Type*} [CommRing T] [Module.Finite ℤ T] (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime) (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) : ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓 := by sorry
