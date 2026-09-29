-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_finrank_pi_eq
-- name    : ModularCurve.DRModelPackageLevel.finrank_pi_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/c40f214f-57c3-5998-9309-d43d24b934b0
-- title:
--   Constant rank q+1 of the degeneracy morphism π
-- statement:
--   Fix an integer $N_0 \neq 0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be an inhabitant of `DRModelPackageLevel N₀ q hqN`. This structure bundles, for the Igusa scheme at level $N_0q$ over $\operatorname{Spec}$ of the coefficient ring `R q`: properness, flatness and local finite presentation of its structure morphism `toBase`, integrality of the source, and integral closedness of the sections over affine opens; a curve model `Meta` of the field `modularFunctionFieldBar (N₀ * q)` over $\overline{\mathbb Q}$ together with an isomorphism `eeta` of its curve onto the base change of `toBase` along $R(q) \to \overline{\mathbb Q}$, compatible with the arithmetic Galois action on places and pinned on the Igusa chart algebra `chartAlgFin (N₀ * q) q`; smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbb Q$; sections $\varepsilon_\infty$, $\varepsilon_0$ of `toBase`; and further data, among them the degeneracy datum $\pi$, namely a morphism $\pi_1$ from the level-$N_0q$ Igusa scheme to the level-$N_0$ one commuting with the two maps to $\operatorname{Spec} R(q)$, together with an $R(q)$-algebra map `iota0` of chart algebras compatible with $\pi_1$ and with Laurent expansions. Assume $\pi_1$ is finite, flat and locally of finite presentation. Then for every point $y$ of the level-$N_0$ Igusa scheme `DRLevel.X0 N₀ q`, the local rank `𝔓.π.1.finrank y` of $\pi_1$ at $y$ equals $q+1$.
--
--   This is the rank part of the assertion that the forgetful (degeneracy) morphism from the model of $X_0(N_0q)$ to that of $X_0(N_0)$ is finite locally free of rank $q+1 = [\Gamma_0(N_0):\Gamma_0(N_0q)]$; the value is the generic degree and is obtained independently of the description of the fibre at $q$. It is combined with the finiteness, flatness and finite-presentation statements in [`ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_finrank_pi_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.finrank_pi_eq (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) [IsFinite 𝔓.π.1] [Flat 𝔓.π.1] [LocallyOfFinitePresentation 𝔓.π.1]
    (y : DRLevel.X0 N₀ q) : 𝔓.π.1.finrank y = q + 1 := by sorry
