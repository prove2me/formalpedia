-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
-- name    : ModularCurve.DRModelPackageLevel.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/e9967b0c-7c32-5009-89bb-be746cfc951b
-- title:
--   Generic unramifiedness of the j-chart over the modular unit line
-- statement:
--   Let $N_0\ge 1$ and let $q$ be a prime with $q\nmid N_0$, and write $R_q=\mathbb{Z}_{(q)}$ for the localisation of $\mathbb{Z}$ used as base. Let $A=$ `IgusaScheme.chartAlgFin (N₀ * q) q`, the $R_q$-subalgebra `chartAlg (N₀*q) q {jFull (N₀*q)}` of the modular function field $F=$ `modularFunctionFieldFull (N₀ * q)` $\subseteq \mathbb{Q}((\mathfrak q))$ attached to the finite-$j$ chart, and let $v\in A$. Assume that the Laurent series over $\mathbb{Q}$ obtained from $v$ through $A\subseteq F\subseteq \mathbb{Q}((\mathfrak q))$ is either `modularUnitSeries q`, namely $\Delta$ divided by its $q$-scaled companion `deltaSeriesN q`, or $q^{12}$ times the inverse of that series. Give $A$ the structure of an $R_q[X]$-algebra by evaluation $X\mapsto v$. The assertion is that there exists a nonzero polynomial $c_0'\in\mathbb{Z}[X]$ such that for every prime ideal $P$ of $A$ whose contraction along $R_q\to A$ is the zero ideal, and with $c_0'(v)\notin P$, the algebra $A$ is unramified over $R_q[X]$ at $P$ in the sense of `Algebra.IsUnramifiedAt`.
--
--   This is the generic-fibre statement that the finite-$j$ chart of the Deligne–Rapoport model is unramified over the affine line coordinatised by Ogg's modular unit $\Delta(\mathfrak q)/\Delta(\mathfrak q^{q})$ (or its partner $q^{12}u^{-1}$) away from the zeros of one fixed nonzero polynomial, i.e. finiteness of the branch locus in characteristic zero. It feeds [`ModularCurve.DRModelPackageLevel.exists_finite_etale_quotient_span_aeval`](thm.html#ModularCurve.DRModelPackageLevel.exists_finite_etale_quotient_span_aeval), which produces finite étale quotients of $A$ by level sets of the modular unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
open scoped Polynomial

namespace ModularCurve.DRModelPackageLevel

theorem exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    letI : Algebra (R q)[X] ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := (Polynomial.aeval (R := R q) v).toRingHom.toAlgebra
    ∃ c₀' : ℤ[X], c₀' ≠ 0 ∧ ∀ (P : Ideal ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) [P.IsPrime],
      P.comap (algebraMap (R q) ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) = ⊥ → Polynomial.aeval v c₀' ∉ P →
        Algebra.IsUnramifiedAt (R q)[X] P := by sorry
