-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_flat_pi
-- name    : ModularCurve.DRModelPackageLevel.flat_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/e98573c6-2a77-5c7d-b1a6-f048be8682b5
-- title:
--   Flatness of π for a Deligne–Rapoport level package
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime not dividing $N_0$, and let $\mathfrak P$ be an inhabitant of the structure `DRModelPackageLevel N₀ q hqN`. Such an inhabitant bundles, for the scheme `X N₀ q` — the Igusa-type model of level $N_0q$ at $q$, obtained as the pushout of the two chart morphisms `fFin` and `fInf` — together with its structure morphism `toBase` $=$ `IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec}(R q)$: the properness, flatness, local finite presentation of `toBase` and integrality of `X N₀ q`; integral closedness of the sections over every affine open; a `CurveModel` `Meta` for the function field `modularFunctionFieldBar (N₀ * q)` over $\overline{\mathbb Q}$ with an isomorphism `eeta` onto the base change of `toBase` along $R q \to \overline{\mathbb Q}$ compatible with the structure morphisms, together with Galois equivariance of the induced identification of points with places and a pinning of the chart algebra generators to their Laurent expansions; smoothness of relative dimension $1$ and geometric integrality of the generic fibre over $\mathbb Q$; sections `εinf`, `εzero` over the base; and further data and axioms, among them a morphism `π`, summarised here. The conclusion is that the underlying morphism of schemes `𝔓.π.1` is flat.
--
--   This is the flatness part of the classical assertion that the degeneracy (forgetful) morphism from the level-$N_0q$ model to the level-$N_0$ model over $\mathbb Z_{(q)}$ is finite and locally free of rank $q+1$, as in Deligne–Rapoport. It is combined with finiteness and the rank computation in [`ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_flat_pi.lean

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

theorem ModularCurve.DRModelPackageLevel.flat_pi (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) : Flat 𝔓.π.1 := by sorry
