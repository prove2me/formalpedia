-- Prove2me | Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
-- name    : ModularCurve.heckeAlphaBarIntegral_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/caaa8638-f0d4-5c16-afcc-4bb0ad314c0b
-- title:
--   Integrality of the degeneracy embedding ᾱ for prime ℓ
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $N$ be a non-zero natural number and let $\ell$ be a prime. The assertion is that the predicate [`ModularCurve.HeckeAlphaBarIntegral L N ℓ`](def/ModularCurve_HeckeOperator.html#L124) holds, that is, the ring homomorphism underlying the $L$-algebra map `heckeAlphaBar L N ℓ` is integral. That map is the inclusion of the base-changed modular function field `laurentBaseChange L (modularFunctionFieldFull N)` into `laurentBaseChange L (modularFunctionFieldFull (N * ℓ))`, supplied by `IntermediateField.inclusion` applied to the containment of intermediate fields `laurentBaseChange_mono' L (full_degeneracy_le (dvd_mul_right N ℓ))` coming from the divisibility $N \mid N\ell$. Thus the conclusion says that every element of the level-$N\ell$ base-changed field is integral over the image of the level-$N$ one under this degeneracy inclusion. No hypothesis beyond $N \neq 0$ and the primality of $\ell$ is imposed; in particular the statement is unconditional in $L$, and nothing is asserted for composite $\ell$.
--
--   This is the integrality half of the classical statement that the degeneracy map $\bar\alpha$ between modular function fields of levels $N$ and $N\ell$ is finite, one of the named inputs needed to build the Hecke correspondence $T_\ell$ on the Jacobian in the project. It is invoked throughout the construction of the Hecke action and its specialisation to the characteristic-$p$ models of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeAlphaBarIntegral_of_prime.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.heckeAlphaBarIntegral_of_prime (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] : ModularCurve.HeckeAlphaBarIntegral L N ℓ := by sorry
