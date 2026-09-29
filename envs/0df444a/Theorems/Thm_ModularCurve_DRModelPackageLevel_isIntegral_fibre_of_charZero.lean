-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero
-- name    : ModularCurve.DRModelPackageLevel.isIntegral_fibre_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/85d8b078-9710-5601-8aa4-80518fc38a2f
-- title:
--   Characteristic-zero fibres of the level-N₀q model are integral
-- statement:
--   Let $N_0$ be a non-zero natural number and $q$ a prime with $q \nmid N_0$, and let $\mathfrak{P}$ be a term of `DRModelPackageLevel N₀ q hqN`, that is, a package of data and properties for the scheme `X N₀ q` over $\operatorname{Spec}(R_q)$, where $R_q$ is the localisation of $\mathbb{Z}$ at the prime $(q)$: the structure morphism `toBase N₀ q`, which is the Igusa morphism `IgusaScheme.igusaTo (N₀ * q) q`, is proper, flat and locally of finite presentation, `X N₀ q` is integral and has integrally closed sections on every affine open, together with a `CurveModel` over $\overline{\mathbb{Q}}$ for the function field `modularFunctionFieldBar (N₀ * q)` identified with the base change of `toBase N₀ q` to $\overline{\mathbb{Q}}$ compatibly with the Galois action and with the chart algebra `IgusaScheme.chartAlgFin (N₀ * q) q`, smoothness of relative dimension $1$ and geometric integrality of the base change to $\mathbb{Q}$, cusp sections over the base, and further data summarised in the structure. Let $k$ be a field of characteristic zero and $\mathrm{to}\kappa \colon R_q \to k$ a ring homomorphism. Then the scheme `fibre toκ`, the pullback of `toBase N₀ q` along $\operatorname{Spec}(\mathrm{to}\kappa)$, is integral, i.e. irreducible and reduced.
--
--   This is the characteristic-zero case of the statement that the fibres of the Deligne–Rapoport model of level $N_0q$ over $\mathbb{Z}_{(q)}$ are integral; it feeds the analysis of connected components of base changes of this model, used in the study of the fibre at $q$ of $X_0(N_0q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isIntegral_fibre_of_charZero.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem isIntegral_fibre_of_charZero
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [CharZero k] (toκ : R q →+* k) :
    IsIntegral (fibre (N₀ := N₀) toκ) := by sorry
