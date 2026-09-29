-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_levelPolynomials_of_chartAlgFin
-- name    : ModularCurve.XHDRModelAtP.exists_levelPolynomials_of_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/144e8588-4443-5739-a443-550c56a67c6a
-- title:
--   Pools of level polynomials on the j-finite chart ring
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$ and $p^2\nmid M$, and a subgroup $H\le(\mathbb Z/M)^\times$ containing the whole kernel of the reduction map $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$; assume the $q$-expansion $j(q)$ of `jqModC` lies in the full-level $q$-expansion function field $\mathbb Q(\mathrm{intFormRatiosC})$ inside $\mathbb Q((q))$, and fix a bundled model datum $\mathfrak X$ of type `XHDRModelAtP p M H hpM hj` (a proper, flat, integral, normal two-chart model over $R_p=\mathbb Z_{(p)}$ of the function field of `ΓM M H`, with smooth generic fibre, a geometric curve model and $q$-expansion and Galois compatibilities). Let $\mathcal O_{\mathrm{fin}}=$ `chartAlgFin` be the $j$-finite chart algebra, i.e. the elements of the function field of `ΓM M H` integral over $R_p[j]$. Let $v\in\mathcal O_{\mathrm{fin}}$ have $q$-expansion either $\Delta(q)/\Delta(q^p)$ (`modularUnitSeries p`) or $p^{12}\Delta(q^p)/\Delta(q)$, and let $v'\in\mathcal O_{\mathrm{fin}}$ satisfy $vv'=p^{12}$. Then for all naturals $A_0,B_0,n_0$ there exist $b$ and $N_1>A_0b^{n_0}+B_0$, monic $g_0,\dots,g_{N_1-1}\in\mathbb Z[X]$ and ranks $r_i$ such that each $\mathcal O_{\mathrm{fin}}/(g_i(v))$ is a finite, étale, free $R_p$-algebra of rank $r_i$ with $1\le r_i\le b$, the ideals $(g_i(v))$ are pairwise comaximal, $(g_i(v))+(g_j(v'))=(1)$ for all $i,j$, and $(g_i(v))+(v)=(1)$ for all $i$.
--
--   This produces, on the $j$-finite chart of the $\Gamma_H(M)$ Deligne–Rapoport-type model over $\mathbb Z_{(p)}$ with $p$ exactly dividing $M$, an arbitrarily large supply of monic integral "level polynomials" cutting out pairwise disjoint finite étale $\mathbb Z_{(p)}$-schemes of bounded rank, disjoint also from the loci cut out by the companion unit $v'$ and by $v$ itself. It is used by the three theorems producing two-sided pools of closed primes in the smooth locus (for $p=2$, $p=3$ and $p\ge5$).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_levelPolynomials_of_chartAlgFin.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel Polynomial
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_levelPolynomials_of_chartAlgFin
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (v : ↥(chartAlgFin p (ΓM M H) hj))
    (hv : ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∨
      ((v : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹)
    (v' : ↥(chartAlgFin p (ΓM M H) hj)) (hvv' : v * v' = (p : ↥(chartAlgFin p (ΓM M H) hj)) ^ 12)
    (A₀ B₀ n₀ : ℕ) :
    ∃ (b N₁ : ℕ) (_ : A₀ * b ^ n₀ + B₀ < N₁) (g : Fin N₁ → ℤ[X]) (rk : Fin N₁ → ℕ),
      (∀ i, (g i).Monic) ∧
      (∀ i, Module.Finite (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Algebra.Etale (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧
        Module.Free (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Module.finrank (R p) (↥(chartAlgFin p (ΓM M H) hj) ⧸ Ideal.span {Polynomial.aeval v (g i)}) = rk i) ∧
      (∀ i, 1 ≤ rk i) ∧ (∀ i, rk i ≤ b) ∧
      (Pairwise fun i j => Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) ∧
      (∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v' (g j)} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) ∧
      (∀ i, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {v} = (⊤ : Ideal ↥(chartAlgFin p (ΓM M H) hj))) := by sorry
