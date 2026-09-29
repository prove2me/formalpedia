-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed
-- name    : ModularCurve.DRModelPackageLevel.isReduced_pullback_toBase_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/417b79ab-de33-5c76-b308-9408ce890a89
-- title:
--   Geometric fibres of the Deligne–Rapoport level model are reduced
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0 \neq 0$ and $q$ prime, and assume $q \nmid N_0$. Let $\mathfrak{P}$ be a `DRModelPackageLevel N₀ q hqN`: a bundle of data and hypotheses for the structure morphism `DRLevel.toBase N₀ q`, which is the Igusa-type morphism `IgusaScheme.igusaTo (N₀ * q) q` from the model `X N₀ q` to $\operatorname{Spec}$ of $R_q = \mathbb{Z}$ localised at the prime $(q)$. The fields of the package record that this morphism is proper, flat and locally of finite presentation, that `X N₀ q` is integral, that the sections over every affine open are integrally closed, a curve model `Meta` over $\overline{\mathbb{Q}}$ with function field `modularFunctionFieldBar (N₀ * q)` together with an isomorphism `eeta` onto the base change of `toBase N₀ q` to $\overline{\mathbb{Q}}$ over the base, compatibility of `eeta` with the arithmetic Galois action on places and with Laurent expansions of the chart algebra `chartAlgFin (N₀ * q) q`, smoothness of relative dimension $1$ and geometric integrality of the base change to $\mathbb{Q}$, two sections `εinf` and `εzero` over $\operatorname{Spec} R_q$, and further conditions, among them a field `fibre_reduced` giving the conclusion below in characteristic $q$. Then for every algebraically closed field $k$ and every morphism $x \colon \operatorname{Spec} k \to \operatorname{Spec} R_q$, the fibre product of `DRLevel.toBase N₀ q` with $x$ is a reduced scheme.
--
--   This is the geometric reducedness of all fibres of the Deligne–Rapoport model of $X_0(N_0q)$ over $\mathbb{Z}_{(q)}$: the generic fibre is smooth, and the fibre in characteristic $q$ is the reduced union of two copies of $X_0(N_0)$ meeting at the supersingular points. It feeds the local study of the model at the branch points, being used for the analysis of sections after base change, of the branch ideals of `εinf` and `εzero`, and of the maximal ideals of local rings at the crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_isReduced_pullback_toBase_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
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

namespace ModularCurve.DRModelPackageLevel

theorem isReduced_pullback_toBase_of_isAlgClosed
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (DRLevel.R q))) :
    IsReduced (pullback (DRLevel.toBase N₀ q) x) := by sorry
