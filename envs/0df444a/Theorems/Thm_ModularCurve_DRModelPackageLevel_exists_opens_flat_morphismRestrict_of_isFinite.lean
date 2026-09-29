-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_of_isFinite
-- name    : ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b7084052-bdfe-5e5e-8abf-ad6745556516
-- title:
--   Flatness of a finite surjection over the regular locus
-- statement:
--   Let $N_0, N', q$ be natural numbers with $N_0$ and $N'$ nonzero and $q$ prime, and suppose $q \nmid N_0$ and $q \nmid N'$. Write $X(N_0,q)$ and $X(N',q)$ for the Igusa schemes `DRLevel.X N₀ q` and `DRLevel.X N' q`, each equipped with its structure morphism `DRLevel.toBase` to $\operatorname{Spec} \mathbb{Z}_{(q)}$ (the Igusa morphism `IgusaScheme.igusaTo` at levels $N_0q$, resp. $N'q$, over the localisation [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8)). Assume given inhabitants $\mathfrak{P}$ of `DRModelPackageLevel N₀ q hqN` and $\mathfrak{P}'$ of `DRModelPackageLevel N' q hqN'`; these bundle, for the respective scheme, properness, flatness, integrality and local finite presentation over $\mathbb{Z}_{(q)}$, integral closedness of the sections over each affine open, an isomorphism of the geometric generic fibre with a curve model of the modular function field together with Galois equivariance and a pinning of Laurent coefficients on the Igusa chart, smoothness of relative dimension $1$ and geometric integrality of the generic fibre, and cuspidal sections — summarised here. Let $\pi$ be a morphism $X(N',q) \to X(N_0,q)$ commuting with the two structure morphisms, finite and surjective on underlying points. Then there is an open subscheme $U$ of $X(N_0,q)$ containing every point whose stalk is a regular local ring, such that the restriction of $\pi$ over $U$ is flat and locally of finite presentation.
--
--   This is the semi-global form of the statement that a finite surjection between Deligne–Rapoport models is flat over the regular locus, obtained from the pointwise criterion by taking $U$ to be an open on which flatness and local finite presentation hold. It is used in the construction of the Hecke degeneracy pair [`ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair`](thm.html#ModularCurve.DRModelPackageLevel.exists_heckeDegeneracyPair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_of_isFinite.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open ModularCurve ModularCurve.DRLevel ModularCurve.DRModelPackageLevel

theorem ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_of_isFinite
    (N₀ N' q : ℕ) [NeZero N₀] [NeZero N'] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (hqN' : ¬ q ∣ N')
    (𝔓 : DRModelPackageLevel N₀ q hqN) (𝔓' : DRModelPackageLevel N' q hqN')
    (π : SchemeHomOver (DRLevel.toBase N' q) (DRLevel.toBase N₀ q)) [IsFinite π.1]
    (hsurj : Function.Surjective π.1.base) :
    ∃ U : (DRLevel.X N₀ q).Opens,
      (∀ x : ↥(DRLevel.X N₀ q), IsRegularLocalRing ((DRLevel.X N₀ q).presheaf.stalk x) → x ∈ U) ∧
      Flat (π.1 ∣_ U) ∧ LocallyOfFinitePresentation (π.1 ∣_ U) := by sorry
