-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_pullback_specMap_rat_le_one
-- name    : ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_pullback_specMap_rat_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/313379c7-9502-5af4-a247-3d1b06c7e016
-- title:
--   Stalks of the generic fibre have Krull dimension at most one
-- statement:
--   Fix a natural number $N_0 \neq 0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a term of the structure `DRModelPackageLevel N₀ p hpN₀`: a package consisting of the Igusa scheme $X(N_0,p)$ together with its structure morphism `toBase N₀ p` $=$ `IgusaScheme.igusaTo (N₀ * p) p` $\colon X(N_0,p) \to \operatorname{Spec}(R_p)$, instances making this morphism proper, flat and locally of finite presentation and the source integral, integral closedness of the sections over every affine open, a curve model `Meta` of the modular function field over $\overline{\mathbb{Q}}$ with an isomorphism `eeta` onto the base change of `toBase N₀ p` to $\overline{\mathbb{Q}}$ compatible with the projection, Galois equivariance and chart-normalisation conditions relating closed points to places and the chart algebra to Laurent coefficients, the assertions that the projection `pullback.snd` of the base change to $\mathbb{Q}$ is smooth of relative dimension $1$ and geometrically integral, sections $\varepsilon_\infty, \varepsilon_0$ over the base, and further data (summarised here). Let $y$ be a point of the fibre product of `toBase N₀ p` and $\operatorname{Spec}$ of the algebra map $R_p \to \mathbb{Q}$. Then the Krull dimension of the stalk of that fibre product at $y$ is at most $1$.
--
--   This records that the generic fibre of the Deligne–Rapoport model, the base change of the Igusa scheme from $R_p$ to $\mathbb{Q}$, has one-dimensional local rings, as befits a curve over $\mathbb{Q}$. It is used in the analysis of fibrewise algebra isomorphisms for the normed Hecke/Poincaré construction, via [`ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare`](thm.html#ModularCurve.DRModelPackageLevel.fibrewiseAlgEquivZero_ofInvertible_norm_pullback_poincare).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_ringKrullDim_stalk_pullback_specMap_rat_le_one.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.ringKrullDim_stalk_pullback_specMap_rat_le_one
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (y : ↥(pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))) :
    ringKrullDim ((pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).presheaf.stalk y) ≤ 1 := by sorry
