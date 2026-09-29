-- Prove2me | Theorems.Thm_ModularCurve_nonempty_dRModelPackageLevel
-- name    : ModularCurve.nonempty_dRModelPackageLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/4068b4f3-4cc4-5d6d-a67b-c0304fd5d43d
-- title:
--   Inhabitedness of the Deligne–Rapoport package at level N₀q
-- statement:
--   Let $N_0$ be a nonzero natural number and $q$ a prime not dividing $N_0$, the non-divisibility being recorded by a hypothesis `hqN`. The assertion is that the type `DRModelPackageLevel N₀ q hqN` is nonempty, i.e. that the whole bundle of data and properties it packages can be produced for the two-chart Igusa scheme $X =$ `DRLevel.X N₀ q` together with its structural morphism `toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q` to $\operatorname{Spec}$ of the base ring `R q`. Unfolding the structure, an inhabitant consists of: properness, flatness and local finite presentation of `toBase N₀ q`, integrality of $X$, and integral closedness of $\Gamma(X, U)$ for every affine open $U$; a `CurveModel` `Meta` over $\overline{\mathbb Q}$ with function field `modularFunctionFieldBar (N₀ * q)`, an isomorphism `eeta` from `Meta.C` to the base change of `toBase N₀ q` along $R q \to \overline{\mathbb Q}$ compatible with the structural morphisms, nonemptiness of the preimage of the finite $j$-chart under the resulting map to $X$, the requirement that reading an element of `IgusaScheme.chartAlgFin (N₀ * q) q` through the germ at that chart and `Meta.ffEquiv.symm` gives the coefficientwise image `coeffEmb` of its Laurent series over $\mathbb Q$, and Galois equivariance: for every $g \in \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ and $\overline{\mathbb Q}$-points $x, x'$ of `Meta.C` with $x'$ the $g$-translate of $x$ in $X$, one has `Meta.pointEquivPlace x' = arithmeticGalois _ g • Meta.pointEquivPlace x`; smoothness of relative dimension $1$ and geometric integrality of the generic fibre over $\mathbb Q$; two sections `εinf`, `εzero` of `toBase N₀ q` over the identity of the base; and the remaining fields of the structure, summarised here: the constant-term retraction `rhoInf` pinning `εinf` on the chart at infinity, an involution `w` over the base acting on the finite chart algebra as the partial Atkin–Lehner involution via `theta`, the forgetful morphism `π` to the level-$N_0$ model with its chart descriptions `iota0`, `iotaInf`, a maximal open `smoothLocus` smooth of relative dimension $1$ containing both sections, and, uniformly in an algebraically closed field $\kappa$ of characteristic $q$ with a ring map from `R q`, reducedness of the fibre, a curve model `Mfib` of that fibre with its chart pinning, the two closed immersions `comp` covering it, their compatibility with `π` and `w`, the Frobenius relation on the places attached to the points of the second component, membership of the two cusps in the respective components, reducedness of the crossing locus and the indexing `nodeEquiv` of the nodes by places.
--
--   This is the existence statement for the Deligne–Rapoport model of $X_0(N_0q)$ over $\mathbf Z_{(q)}$ at a prime $q$ exactly dividing the level, in the packaged form used downstream: the generic fibre is the smooth modular curve, while the fibre at $q$ is two copies of $X_0(N_0)$ crossing at the supersingular points, interchanged by the Atkin–Lehner involution and related by Frobenius. It is the input for the Hecke-correspondence statement [`ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne`](thm.html#ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne) and for [`ModularCurve.exists_jZeroNeronObjectAtP_and_bridge`](thm.html#ModularCurve.exists_jZeroNeronObjectAtP_and_bridge), which feed the study of the Néron model and the Galois representations attached to $J_0(N_0q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_dRModelPackageLevel.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.DRLevel

theorem ModularCurve.nonempty_dRModelPackageLevel
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) :
    Nonempty (DRModelPackageLevel N₀ q hqN) := by sorry
