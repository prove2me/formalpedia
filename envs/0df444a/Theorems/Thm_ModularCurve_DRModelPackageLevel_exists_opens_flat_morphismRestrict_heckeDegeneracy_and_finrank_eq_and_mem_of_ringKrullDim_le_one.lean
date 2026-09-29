-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one
-- name    : ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/b986318f-b1d3-5efa-872f-84b11207bff6
-- title:
--   Finite flat locus of π₂ in codimension ≤ 1
-- statement:
--   Fix a natural number $N_0 \ne 0$ and a prime $p$ with $p \nmid N_0$, and let $\mathfrak{P}$ be a Deligne–Rapoport model package `DRModelPackageLevel N₀ p hpN₀`; among its data are that the structure morphism `toBase N₀ p` $: X(N_0,p) \to \operatorname{Spec} R_p$ (over the localisation $R_p \subset \mathbf{Q}$ of $\mathbf{Z}$ at the primes other than $p$) is proper, flat and locally of finite presentation, that $X(N_0,p)$ is integral, that $\Gamma(X(N_0,p),U)$ is integrally closed for every affine open $U$, together with the further fields of the package (a curve model over $\overline{\mathbf{Q}}$ with its Galois compatibilities, generic smoothness and geometric integrality, cusp sections, and so on). Let $\ell$ be a prime and let $\pi_2$ be a morphism $X(N_0\ell,p) \to X(N_0,p)$ whose composite with `toBase N₀ p` equals `toBase (N₀ * ℓ) p`, assumed finite and surjective; no modular interpretation of $\pi_2$ is imposed. Let $D$ be a relative $\operatorname{Pic}^0$ designation over $R_p$ for `toBase N₀ p`, that is a scheme $P$ with a morphism to $\operatorname{Spec} R_p$ together with a section of it, and assume the fibre product of `toBase (N₀ * ℓ) p` with $D$'s structure morphism is integral. Then there are an open $V \subseteq X(N_0,p)$ and $d \in \mathbf{N}$ such that the restriction $\pi_2 \mid_V$ is flat and locally of finite presentation, its fibre rank at every point of $V$ equals $d$, and every $x \in X(N_0,p)$ whose local ring has Krull dimension $\le 1$ lies in $V$.
--
--   This is the statement that a finite surjective map of Deligne–Rapoport models over $\mathbf{Z}_{(p)}$ becomes finite locally free of constant rank on an open set containing all points of codimension $\le 1$, the normality-plus-finiteness input used later to push and pull line bundles along a degeneracy map. It is cited in the construction of the Hecke homomorphism on relative Picard schemes and in the fibrewise analysis of norms of pullbacks of the Poincaré bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel

theorem ModularCurve.DRModelPackageLevel.exists_opens_flat_morphismRestrict_heckeDegeneracy_and_finrank_eq_and_mem_of_ringKrullDim_le_one
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (π₂ : SchemeHomOver (toBase (N₀ * ℓ) p) (toBase N₀ p)) [IsFinite π₂.1] [Surjective π₂.1]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    [IsIntegral ↑(pullback (toBase (N₀ * ℓ) p) D.toBase)] :
    ∃ (V : (X N₀ p).Opens) (d : ℕ), Flat (π₂.1 ∣_ V) ∧ LocallyOfFinitePresentation (π₂.1 ∣_ V) ∧
      (∀ y : V, (π₂.1 ∣_ V).finrank y = d) ∧
      ∀ x : X N₀ p, ringKrullDim ((X N₀ p).presheaf.stalk x) ≤ 1 → x ∈ V := by sorry
