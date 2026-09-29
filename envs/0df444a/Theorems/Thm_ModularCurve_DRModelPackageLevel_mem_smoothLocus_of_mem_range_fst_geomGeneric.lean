-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric
-- name    : ModularCurve.DRModelPackageLevel.mem_smoothLocus_of_mem_range_fst_geomGeneric
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/1165950c-9b9a-5f05-b26a-779949a675aa
-- title:
--   Geometric generic points lie in the smooth locus
-- statement:
--   Fix a natural number $N_0 \ne 0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak P$ be a term of `DRModelPackageLevel N₀ p hpN₀`, that is, a bundle of data and properties for the Igusa scheme $X(N_0,p)$ together with its structure morphism `toBase N₀ p` to $\operatorname{Spec}$ of the coefficient ring `R p`; among the fields of such a package are properness, flatness, integrality and local finite presentation of `toBase N₀ p`, a curve model of the function field over $\overline{\mathbf Q}$ identified with the geometric generic fibre, smoothness of relative dimension $1$ and geometric integrality of the fibre over $\mathbf Q$, and an open subscheme `𝔓.smoothLocus` of $X(N_0,p)$ which is maximal among opens whose restricted structure morphism is smooth over the base. Let $x$ be a point of the underlying topological space of $X(N_0,p)$ and assume that $x$ lies in the image of the map on topological spaces induced by the first projection of the fibre product of `toBase N₀ p` with $\operatorname{Spec}$ of the structure map $\mathrm{R}\,p \to \overline{\mathbf Q}$, i.e. that $x$ is the image of a point of the geometric generic fibre. The conclusion is that $x$ belongs to the set of points of `𝔓.smoothLocus`.
--
--   This is the statement that the image in the Deligne–Rapoport model of $X_0(N_0p)$ over the local base of the geometric generic fibre is contained in the smooth locus of the model, the generic-fibre half of the description of where the model is smooth. It is used when integral sections and divisors are placed inside the smooth locus, where such divisors are Cartier, in the construction of Hecke correspondences and in the statements on extension of divisor classes to places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing
  ModularCurve ModularCurve.DRLevel

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.mem_smoothLocus_of_mem_range_fst_geomGeneric
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (x : ↥(X N₀ p))
    (hx : x ∈ Set.range (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).base) :
    x ∈ (𝔓.smoothLocus : Set (X N₀ p)) := by sorry
