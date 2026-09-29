-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_levelPolynomials_of_chartAlgFin
-- name    : ModularCurve.DRModelPackageLevel.exists_levelPolynomials_of_chartAlgFin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/4ec5edcd-b7cf-54b9-8352-114de550f915
-- title:
--   Level polynomials for Ogg's unit on the Igusa chart
-- statement:
--   Fix a nonzero natural number $N_0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN` for level $N_0q$. Let $A$ denote the Igusa chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q`, a subalgebra of the modular function field `modularFunctionFieldFull (N₀ * q)` over the base ring `R q`. Let $v \in A$ be an element whose Laurent series is either `modularUnitSeries q`, that is $\Delta(\tau)/\Delta(q\tau)$, or $q^{12}$ times the inverse of that series, and let $v' \in A$ satisfy $v v' = q^{12}$. Let $A_0, B_0, n_0$ be natural numbers. Then there exist natural numbers $b$ and $M$ with $A_0 b^{n_0} + B_0 < M$, a family $g : \mathrm{Fin}\,M \to \mathbb{Z}[X]$ and ranks $rk : \mathrm{Fin}\,M \to \mathbb{N}$ such that each $g_i$ is monic; each quotient $A/(g_i(v))$ is a finite, étale and free `R q`-algebra of `R q`-rank $rk_i$; $1 \le rk_i \le b$ for all $i$; the ideals $(g_i(v))$ are pairwise comaximal, that is $(g_i(v)) + (g_j(v)) = A$ for $i \ne j$; $(g_i(v)) + (g_j(v')) = A$ for all $i$ and $j$, including $i = j$; and $(g_i(v)) + (v) = A$ for every $i$.
--
--   This is the commutative-algebra half of the construction of a large family of level sets of Ogg's modular unit $\Delta(\tau)/\Delta(q\tau)$ on the finite-$j$ chart of the Deligne–Rapoport model of level $N_0q$: it produces arbitrarily many finite étale free level rings whose defining ideals are pairwise comaximal and also comaximal with the ideals cut out by the Atkin–Lehner partner $v'$ and with $(v)$ itself. It is used in the construction of two-sided pools of closed primes in the smooth locus, in the variants `exists_twoSidedPool_smoothLocus_closedPrime_two`, `exists_twoSidedPool_smoothLocus_closedPrime_three` and `exists_twoSidedPool_smoothLocus_closedPrime_of_five_le`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_levelPolynomials_of_chartAlgFin.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped Polynomial

namespace ModularCurve.DRModelPackageLevel

theorem exists_levelPolynomials_of_chartAlgFin
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹)
    (v' : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (hvv' : v * v' = (q : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) ^ 12)
    (A₀ B₀ n₀ : ℕ) :
    ∃ (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M) (g : Fin M → ℤ[X]) (rk : Fin M → ℕ),
      (∀ i, (g i).Monic) ∧
      (∀ i, Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧
        Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) ∧ Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v (g i)}) = rk i) ∧
      (∀ i, 1 ≤ rk i) ∧ (∀ i, rk i ≤ b) ∧
      (Pairwise fun i j => Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v (g j)} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ∧
      (∀ i j, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {Polynomial.aeval v' (g j)} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) ∧
      (∀ i, Ideal.span {Polynomial.aeval v (g i)} ⊔ Ideal.span {v} = (⊤ : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q))) := by sorry
