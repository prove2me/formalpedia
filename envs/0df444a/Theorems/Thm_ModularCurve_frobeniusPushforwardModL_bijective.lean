-- Prove2me | Theorems.Thm_ModularCurve_frobeniusPushforwardModL_bijective
-- name    : ModularCurve.frobeniusPushforwardModL_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/cf23c059-2c30-5398-b581-d17a821ea14b
-- title:
--   Bijectivity of the Frobenius push-forward on J₀(N) in characteristic ℓ
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime, and let $K$ have characteristic $\ell$; let $N$ be a natural number with $N \neq 0$. Write $F =$ `modularFunctionFieldFullC K N` for the full level-$N$ modular function field over $K$ and $J_0(N)_K =$ `JZeroC K N`, defined as $\mathrm{Pic}^0$ of $F$ over $K$, an additive commutative group. The endomorphism `frobeniusPushforwardModL K N ℓ` of $J_0(N)_K$ is defined by cases on the predicate `FrobeniusInputsModL K N ℓ`, which asserts the existence of data `HasPrincipalDivisors K F` and a finiteness witness `FiniteAlong K (frobeniusModL K N ℓ)` for which both `FundamentalIdentityAlong` and `NormFormulaAlong` hold along the Frobenius map `frobeniusModL K N ℓ`: when that predicate holds, it is the map induced on degree-zero divisor classes by the divisor push-forward `frobeniusDegZeroPushforwardModL K N ℓ` (well defined because push-forward along the Frobenius carries principal divisors to principal divisors), and otherwise it is the zero homomorphism. The assertion is that this additive group homomorphism $J_0(N)_K \to J_0(N)_K$ is bijective as a function. Since $K$ is algebraically closed, [`ModularCurve.frobeniusInputsModL`](thm.html#ModularCurve.frobeniusInputsModL) guarantees that the first branch applies, so the statement concerns the genuine push-forward and not the zero map.
--
--   This is the statement that the geometric Frobenius push-forward $\mathrm{Fr}_*$ on the Jacobian $J_0(N)$ of the modular curve over an algebraically closed field of characteristic $\ell$ is a bijection, reflecting that the Frobenius extension of the modular function field is purely inseparable. It is used in [`ModularCurve.frobeniusPushforwardModL_frobeniusPullbackModL`](thm.html#ModularCurve.frobeniusPushforwardModL_frobeniusPullbackModL), which compares the push-forward with the pull-back along the same map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusPushforwardModL_bijective.lean

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.frobeniusPushforwardModL_bijective
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (N : ℕ) [NeZero N] :
    Function.Bijective (frobeniusPushforwardModL K N ℓ) := by sorry
