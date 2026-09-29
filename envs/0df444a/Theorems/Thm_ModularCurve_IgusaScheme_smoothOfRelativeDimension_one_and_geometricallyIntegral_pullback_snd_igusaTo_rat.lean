-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_and_geometricallyIntegral_pullback_snd_igusaTo_rat
-- name    : ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_and_geometricallyIntegral_pullback_snd_igusaTo_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/1a06ec8e-40a0-5791-aba1-8c2329672c89
-- title:
--   Generic fibre of the Igusa scheme is smooth and geometrically integral
-- statement:
--   Let $N \ge 1$ and let $\ell$ be a prime. Write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$, and let $F$ be the full modular function field of level $N$. The scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout of the two morphisms `fFin N ℓ` and `fInf N ℓ`, the maps of spectra induced by the inclusions of the two chart algebras $\mathbb{Z}_{(\ell)}$-subalgebras `chartAlgFin N ℓ` $=$ `chartAlg N ℓ {jFull N}` and `chartAlgInf N ℓ` $=$ `chartAlg N ℓ {(jFull N)⁻¹}` of $F$ into the middle ring, and `igusaTo N ℓ` is the structure morphism to $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ obtained from the two structure maps $\mathbb{Z}_{(\ell)} \to$ `chartAlgFin N ℓ`, `chartAlgInf N ℓ` by the universal property of the pushout. The assertion is that the second projection of the fibre product of `igusaTo N ℓ` with the morphism $\operatorname{Spec}\mathbb{Q} \to \operatorname{Spec}\mathbb{Z}_{(\ell)}$ induced by the inclusion $\mathbb{Z}_{(\ell)} \hookrightarrow \mathbb{Q}$, i.e. the generic fibre $X_{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$, is both smooth of relative dimension $1$ and geometrically integral. No coprimality between $\ell$ and $N$ is assumed.
--
--   This is the statement that Igusa's two-chart integral model of the modular curve of level $N$ over $\mathbb{Z}_{(\ell)}$ has, in characteristic zero, a smooth geometrically integral curve as generic fibre; because the assertion concerns the $\mathbb{Q}$-fibre only, it holds for every prime $\ell$, including those dividing $N$. It feeds the construction of sections over the smooth locus ([`ModularCurve.IgusaScheme.exists_smoothLocus_maximal_and_section_mem`](thm.html#ModularCurve.IgusaScheme.exists_smoothLocus_maximal_and_section_mem)) and the production of the Deligne–Rapoport model package used later in the argument ([`ModularCurve.nonempty_dRModelPackageLevel`](thm.html#ModularCurve.nonempty_dRModelPackageLevel)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_and_geometricallyIntegral_pullback_snd_igusaTo_rat.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModularCurve
open ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_and_geometricallyIntegral_pullback_snd_igusaTo_rat
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) ∧
    GeometricallyIntegral
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) := by sorry
