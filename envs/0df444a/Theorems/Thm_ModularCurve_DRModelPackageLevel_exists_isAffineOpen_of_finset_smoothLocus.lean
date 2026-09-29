-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_isAffineOpen_of_finset_smoothLocus
-- name    : ModularCurve.DRModelPackageLevel.exists_isAffineOpen_of_finset_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b8d914bd-7874-592d-8ad8-69591297c3df
-- title:
--   Finite subsets of the smooth locus over an affine open lie in an affine open
-- statement:
--   Fix natural numbers $N_0$ and $q$ with $N_0 \neq 0$ and $q$ prime, and assume $q \nmid N_0$; let $\mathfrak{P}$ be a Deligne–Rapoport level package `DRModelPackageLevel N₀ q hqN` for the curve $X_{N_0,q}$ over $\mathrm{Spec}$ of the ring `R q`, whose structure morphism is `toBase N₀ q`, the morphism `IgusaScheme.igusaTo (N₀ * q) q` from the Igusa scheme (a pushout of two affine charts) to $\mathrm{Spec}(\mathtt{R}\,q)$. Write $U = \mathfrak{P}.\mathtt{smoothLocus}$ for the open of $X_{N_0,q}$ carried by the package, with open immersion $\iota$, regarded as a scheme. The assertion is: for every affine open $V$ of $\mathrm{Spec}(\mathtt{R}\,q)$ (an element of the type of affine opens, so an open together with the proof that it is affine) and every finite set $F$ of points of the scheme $U$ such that the composite of $\iota$ with `toBase N₀ q` sends every $x \in F$ into $V$, there exists an open $W$ of the scheme $U$ such that $W$ is an affine open, $W$ is contained in the preimage of $V$ under that composite, and every $x \in F$ lies in $W$.
--
--   This is the form needed of the classical fact that any finite set of points of a quasi-projective scheme admits a common affine open neighbourhood, here localised so that the neighbourhood may be taken inside the smooth locus of the Deligne–Rapoport level model and above a prescribed affine open of the base. It is used in the construction underlying [`ModularCurve.DRModelPackageLevel.exists_representsRelSubPic`](thm.html#ModularCurve.DRModelPackageLevel.exists_representsRelSubPic), where relative divisor classes must be computed on affine opens lying over affine opens of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_isAffineOpen_of_finset_smoothLocus.lean

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve TensorProduct
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

namespace ModularCurve.DRModelPackageLevel

theorem exists_isAffineOpen_of_finset_smoothLocus (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN) :
    ∀ (V : (Spec (CommRingCat.of (R q))).affineOpens) (F : Finset ↥𝔓.smoothLocus),
      (∀ x ∈ F, (𝔓.smoothLocus.ι ≫ toBase N₀ q).base x ∈ (V : (Spec (CommRingCat.of (R q))).Opens)) →
      ∃ W : (𝔓.smoothLocus : Scheme.{0}).Opens, IsAffineOpen W ∧
        W ≤ (𝔓.smoothLocus.ι ≫ toBase N₀ q) ⁻¹ᵁ (V : (Spec (CommRingCat.of (R q))).Opens) ∧ ∀ x ∈ F, x ∈ W := by sorry
