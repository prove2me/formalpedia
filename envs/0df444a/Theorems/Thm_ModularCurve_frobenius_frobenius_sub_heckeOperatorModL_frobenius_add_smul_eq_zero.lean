-- Prove2me | Theorems.Thm_ModularCurve_frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero
-- name    : ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/0a4266d6-93f5-5468-b0aa-6d906f24ab88
-- title:
--   Eichler–Shimura relation for Fr_* on J₀(N) in characteristic ℓ
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime with $\operatorname{char} K = \ell$, and $N$ a nonzero natural number with $\ell \nmid N$. Write $\bar F_N =$ `modularFunctionFieldFullC K N` for the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the family `divisorExpansionsC K N` of $q$-expansions attached to the divisors of $N$, and let `JZeroC K N` $= \mathrm{Pic}^0$ of $\bar F_N$ over $K$, that is, the group of degree-zero divisors of $\bar F_N/K$ modulo the subgroup of principal divisors contained in it. Two additive endomorphisms of this group are in play: `frobeniusPushforwardModL K N ℓ`, equal to the pushforward of divisor classes along the Frobenius `frobeniusModL K N ℓ` of $\bar F_N$ whenever the predicate `FrobeniusInputsModL K N ℓ` holds (existence of principal divisors for $\bar F_N$, finiteness along the Frobenius, and the fundamental identity and the norm formula along it) and equal to $0$ otherwise, and `heckeOperatorModL K N ℓ`, defined as the sum of that pushforward and the corresponding pullback `frobeniusPullbackModL K N ℓ`. The assertion is that for every class $y$ in `JZeroC K N`,
--   $$\mathrm{Fr}_*(\mathrm{Fr}_*(y)) - \bar T_\ell(\mathrm{Fr}_*(y)) + \ell\, y = 0,$$
--   where $\mathrm{Fr}_*$ is the pushforward, $\bar T_\ell$ the above operator, and $\ell\, y$ the $\mathbb{N}$-scalar multiple. Since $\bar T_\ell = \mathrm{Fr}_* + \mathrm{Fr}^*$ by definition, this is the same as $\mathrm{Fr}^*\circ\mathrm{Fr}_* = \ell$ on degree-zero divisor classes.
--
--   This is the Eichler–Shimura congruence relation in the form it takes on the special fibre of $J_0(N)$ at a prime $\ell$ of good reduction: the quadratic relation satisfied by the Frobenius pushforward against the mod-$\ell$ Hecke operator $\bar T_\ell$. It is used downstream in the analysis of the Frobenius action on the Tate module of $J_0(N)$ and of eigenplanes therein, and in the statements about torsion, specialisation kernels and finite flat models of $J_0(N)$ in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) (y : ModularCurve.JZeroC K N) :
    ModularCurve.frobeniusPushforwardModL K N ℓ (ModularCurve.frobeniusPushforwardModL K N ℓ y)
      - ModularCurve.heckeOperatorModL K N ℓ (ModularCurve.frobeniusPushforwardModL K N ℓ y)
      + ℓ • y = 0 := by sorry
