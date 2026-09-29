-- Prove2me | Theorems.Thm_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime
-- name    : Module.exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/67a93726-0983-5db1-bfeb-838e66bb8505
-- title:
--   Base change of a finite-length module is killed by a power of mathfrak m_B
-- statement:
--   Let $S$ be a commutative ring and let $H$ be an $S$-module which is of finite length in the sense of Mathlib's `IsFiniteLength` predicate (equivalently, $H$ is both Noetherian and Artinian as an $S$-module). Let $\mathfrak p$ be a prime ideal of $S$, and let $B$ be a commutative ring equipped with an $S$-algebra structure which realises the localisation of $S$ at $\mathfrak p$, i.e. `IsLocalization.AtPrime B 𝔭` holds for the complement of $\mathfrak p$, and which is a local ring. Then there exists a natural number $n$ such that the maximal ideal of $B$ satisfies $$\mathfrak m_B^{\,n} \cdot \bigl(B \otimes_S H\bigr) = 0,$$ that is, the $n$-th power of $\mathfrak m_B$ annihilates the whole of the base-changed $B$-module $B \otimes_S H$ (the submodule $\mathfrak m_B^n \bullet \top$ of $B \otimes_S H$ is the zero submodule). The hypothesis on $\mathfrak p$ is primality only; maximality is not assumed, and no finiteness hypothesis is placed on $S$ itself.
--
--   This is the standard statement that a finite-length module becomes annihilated by a power of the maximal ideal after localising at a prime, here in the form of a base change $B \otimes_S H$ along an arbitrary localisation of $S$ at $\mathfrak p$. It is used in the treatment of polarisations, to show that a power of the maximal ideal kills the relevant stalk of a Čech slice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open TensorProduct

theorem Module.exists_pow_maximalIdeal_smul_top_baseChange_eq_bot_of_isFiniteLength_of_isPrime
    (S : Type u) [CommRing S] (H : Type v) [AddCommGroup H] [Module S H] (hH : IsFiniteLength S H)
    (𝔭 : Ideal S) [𝔭.IsPrime]
    (B : Type w) [CommRing B] [Algebra S B] [IsLocalization.AtPrime B 𝔭] [IsLocalRing B] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal B ^ n • (⊤ : Submodule B (B ⊗[S] H)) = ⊥ := by sorry
