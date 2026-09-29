-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre
-- name    : ModularCurve.DRModelPackageLevel.not_isOpen_singleton_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/777d1ada-0ce4-532b-ad3b-0ac6309e9782
-- title:
--   No isolated points in the geometric fibre at q
-- statement:
--   Fix a positive integer $N_0$ and a prime $q$ with $q \nmid N_0$, and let $\mathfrak P$ be a `DRModelPackageLevel N₀ q hqN`: a bundle of data for the Igusa-type scheme `X N₀ q` over $\operatorname{Spec}(\mathrm{R\ q})$ with structure map `toBase N₀ q` $=$ `IgusaScheme.igusaTo (N₀ * q) q`, comprising properness, flatness, local finite presentation of that map and integrality of the source, integral closedness of the sections on affine opens, an isomorphism of the base change to $\overline{\mathbb Q}$ with a curve model whose function field is the base change to $\overline{\mathbb Q}$ of the modular function field of level $N_0q$ together with Galois-equivariance and cusp-normalisation clauses, smoothness of relative dimension one and geometric integrality of the fibre over $\mathbb Q$, cusp sections, and further clauses on the fibre at $q$ and its components, all summarised here. Let $\kappa$ be an algebraically closed field of characteristic $q$ and `toκ` $:$ `R q` $\to \kappa$ a ring homomorphism, and let $w$ be a point of the underlying space of the fibre `DRLevel.fibre toκ`, the pullback of `toBase N₀ q` along $\operatorname{Spec}(\mathrm{to}\kappa)$. Then the singleton $\{w\}$ is not open in that space.
--
--   The assertion is that the geometric fibre at $q$ of the Deligne–Rapoport style model of the modular curve of level $N_0q$ has no isolated points, each of its points lying on a positive-dimensional component. It is used in the construction of flat affine neighbourhoods inside that model, via [`ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_of_isFinite`](thm.html#ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_of_isFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_not_isOpen_singleton_fibre.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.not_isOpen_singleton_fibre
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (toκ : DRLevel.R q →+* κ)
    (w : DRLevel.fibre (N₀ := N₀) toκ) : ¬ IsOpen ({w} : Set (DRLevel.fibre (N₀ := N₀) toκ)) := by sorry
