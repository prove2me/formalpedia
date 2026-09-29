-- Prove2me | Theorems.Thm_ModularCurve_cuspCount_mul_of_coprime
-- name    : ModularCurve.cuspCount_mul_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/8f9c5f09-d4bf-5962-8053-1b58b6a6cf05
-- title:
--   Multiplicativity of the cusp count ν_∞
-- statement:
--   For natural numbers $M$ and $N$ with $M \neq 0$, $N \neq 0$ and $\gcd(M,N) = 1$, the arithmetic function $\mathrm{cuspCount}$ satisfies $\mathrm{cuspCount}(MN) = \mathrm{cuspCount}(M)\cdot\mathrm{cuspCount}(N)$. Here $\mathrm{cuspCount}$ is defined purely arithmetically: for a natural number $N$, $\mathrm{cuspCount}(N)$ is the sum, over the divisors $d$ of $N$ (the Mathlib divisor finset, empty when $N = 0$), of Euler's totient $\varphi\bigl(\gcd(d, N/d)\bigr)$, the division being natural-number division. Thus the assertion is the identity $$\sum_{d \mid MN} \varphi\!\left(\gcd\!\left(d, \tfrac{MN}{d}\right)\right) = \left(\sum_{d \mid M} \varphi\!\left(\gcd\!\left(d, \tfrac{M}{d}\right)\right)\right)\left(\sum_{e \mid N} \varphi\!\left(\gcd\!\left(e, \tfrac{N}{e}\right)\right)\right)$$ for coprime positive $M, N$. No modular curve, congruence subgroup or geometric object enters the statement; it is an identity between sums of totient values over divisor sets.
--
--   The quantity $\mathrm{cuspCount}(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$ is the classical count of cusps of the modular curve $X_0(N)$, and the theorem records that this count is a multiplicative function of the level. It is used in the numerical genus computations of the project, being cited in [`ModularCurve.genusFormula_mul_expand`](thm.html#ModularCurve.genusFormula_mul_expand), [`ModularCurve.FullLevel.genusFF_fieldBar_eq_of_eq_two`](thm.html#ModularCurve.FullLevel.genusFF_fieldBar_eq_of_eq_two) and [`ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq`](thm.html#ModularCurve.FullLevel.two_mul_natCard_doubleCoset_gammaH_levelH_zpowers_T_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cuspCount_mul_of_coprime.lean

import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.cuspCount_mul_of_coprime {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hMN : Nat.Coprime M N) : cuspCount (M * N) = cuspCount M * cuspCount N := by sorry
