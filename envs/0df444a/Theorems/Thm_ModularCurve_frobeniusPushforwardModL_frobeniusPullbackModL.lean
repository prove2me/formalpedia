-- Prove2me | Theorems.Thm_ModularCurve_frobeniusPushforwardModL_frobeniusPullbackModL
-- name    : ModularCurve.frobeniusPushforwardModL_frobeniusPullbackModL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/798948bf-1a03-5119-900b-e93ea2dd211b
-- title:
--   Fr_*Fr^* = ℓ on J₀(N) in characteristic ℓ
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime with $K$ of characteristic $\ell$, and $N$ a nonzero natural number with $\ell \nmid N$. Write $F =$ `modularFunctionFieldFullC K N` for the subfield of the Laurent series field over $K$ generated over $K$ by the divisor expansions of level $N$, and let $J_0(N) =$ `JZeroC K N` be the associated degree-zero divisor class group, i.e. the quotient of the group of degree-zero divisors of $F/K$ by its subgroup of principal divisors. The two endomorphisms $\mathrm{Fr}_* =$ `frobeniusPushforwardModL` and $\mathrm{Fr}^* =$ `frobeniusPullbackModL` of this group are each defined by a case distinction on the predicate `FrobeniusInputsModL K N ℓ`, which packages the existence of a principal-divisor structure on $F$, the finiteness of the Frobenius map `frobeniusModL K N ℓ`, the fundamental identity along it and the norm formula for it: when that predicate holds they are the push-forward and pull-back of divisor classes induced by Frobenius, and otherwise both are the zero homomorphism. The assertion is that for every $y \in J_0(N)$ one has $\mathrm{Fr}_*(\mathrm{Fr}^*(y)) = \ell \cdot y$, the $\ell$-fold sum of $y$ in the divisor class group.
--
--   This is one half of the standard relation $f_* f^* = \deg f$ for the degree-$\ell$ Frobenius morphism, here on the degree-zero class group of the level-$N$ modular function field in characteristic $\ell$; it is the companion of the identity $\mathrm{Fr}^*\mathrm{Fr}_* = \ell$. It is used in the analysis of the Néron model of $J_0(N)$ at $p$, in the comparison of degeneracy maps with the Hecke generator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobeniusPushforwardModL_frobeniusPullbackModL.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.frobeniusPushforwardModL_frobeniusPullbackModL
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) (y : ModularCurve.JZeroC K N) :
    ModularCurve.frobeniusPushforwardModL K N ℓ (ModularCurve.frobeniusPullbackModL K N ℓ y) = ℓ • y := by sorry
