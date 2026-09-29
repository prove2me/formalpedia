-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_finite_etale_quotient_span_aeval
-- name    : ModularCurve.DRModelPackageLevel.exists_finite_etale_quotient_span_aeval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/f7c4d4f1-4a62-5f48-b4a5-f73288a1688b
-- title:
--   Étale level sets of the modular unit Δ(τ)/Δ(qτ)
-- statement:
--   Fix $N_0 \ge 1$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ q hqN`, i.e. the data of the model `X N₀ q` over `Spec (R q)` ($R_q$ the localisation of $\mathbb{Z}$ at $q$) together with properness, flatness, integrality and local finite presentation, normality of its affine sections, a curve model over $\overline{\mathbb{Q}}$ identified with the geometric fibre compatibly with the Galois action and pinned by $q$-expansions, smoothness and geometric integrality of the generic fibre, and the distinguished sections carried by that structure. Let $A$ denote `IgusaScheme.chartAlgFin (N₀ * q) q`, the subalgebra of elements of the modular function field $F =$ `modularFunctionFieldFull (N₀ * q)` integral over $R_q[j]$, and let $v \in A$ be an element whose Laurent expansion is either the modular unit `modularUnitSeries q` $= \Delta/\Delta_q$ or $q^{12}$ times its inverse. Then there exist a nonzero $\mathrm{avoid} \in \mathbb{F}_q[X]$, a nonzero $c_0 \in \mathbb{Z}[X]$ and $K \in \mathbb{N}$ such that for every monic $g \in \mathbb{Z}[X]$ of degree at least $1$ whose reduction mod $q$ is irreducible and coprime to $\mathrm{avoid}$, and which does not divide $c_0$, the quotient $A/(g(v))$ is a finite, étale and free $R_q$-algebra of rank $r$ with $1 \le r \le K \deg g$.
--
--   This produces finite étale multisections of bounded degree on the Deligne–Rapoport model of $X_0(N_0q)$ over $\mathbb{Z}_{(q)}$, cut out by level sets of Ogg's modular unit $\Delta(\tau)/\Delta(q\tau)$ on the finite-$j$ chart. It is used by [`ModularCurve.DRModelPackageLevel.exists_levelPolynomials_of_chartAlgFin`](thm.html#ModularCurve.DRModelPackageLevel.exists_levelPolynomials_of_chartAlgFin), which feeds the construction of the relative Picard data for the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_finite_etale_quotient_span_aeval.lean

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

theorem exists_finite_etale_quotient_span_aeval
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    ∃ (avoid : (ZMod q)[X]) (_ : avoid ≠ 0) (c₀ : ℤ[X]) (_ : c₀ ≠ 0) (K : ℕ),
      ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod q))) →
        IsCoprime (g.map (Int.castRingHom (ZMod q))) avoid → ¬ g ∣ c₀ →
          Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          1 ≤ Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ K * g.natDegree := by sorry
