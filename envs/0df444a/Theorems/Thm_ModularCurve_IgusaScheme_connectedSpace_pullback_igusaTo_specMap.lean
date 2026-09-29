-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap
-- name    : ModularCurve.IgusaScheme.connectedSpace_pullback_igusaTo_specMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/2c8dcb6e-a26d-5c7b-a1c2-58ae733e1876
-- title:
--   Fibres of the Igusa two-chart model are connected
-- statement:
--   Fix an integer $N \ge 1$ and a prime $\ell$, with no condition relating $\ell$ to $N$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator in lowest terms is coprime to $\ell$. Let $L$ be a field equipped with a $\mathbb{Z}_{(\ell)}$-algebra structure. The scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout, in schemes over $\operatorname{Spec}\mathbb{Z}_{(\ell)}$, of the two morphisms `fFin N ℓ` and `fInf N ℓ` obtained by applying $\operatorname{Spec}$ to the inclusions `inclFin N ℓ` and `inclInf N ℓ` of the two charts `chartAlgFin N ℓ` $=$ `chartAlg N ℓ {jFull N}` and `chartAlgInf N ℓ` $=$ `chartAlg N ℓ {(jFull N)⁻¹}`, subalgebras of the field `modularFunctionFieldFull N` over $\mathbb{Z}_{(\ell)}$, into the middle algebra; the morphism `igusaTo N ℓ` to $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ is the one descending from the structure maps $\operatorname{Spec}$ of $\mathbb{Z}_{(\ell)} \to$ `chartAlgFin N ℓ` and $\mathbb{Z}_{(\ell)} \to$ `chartAlgInf N ℓ`. The assertion is that the underlying topological space of the fibre product of `igusaTo N ℓ` with the morphism $\operatorname{Spec} L \to \operatorname{Spec}\mathbb{Z}_{(\ell)}$ induced by the structure map $\mathbb{Z}_{(\ell)} \to L$ is a connected space, that is, non-empty and connected.
--
--   This is the Zariski connectedness of every fibre of the two-chart integral model of the modular curve over $\mathbb{Z}_{(\ell)}$, base-changed to an arbitrary field over $\mathbb{Z}_{(\ell)}$, and so includes the primes $\ell$ dividing the level, where the special fibre need not be irreducible. It underlies [`ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_igusaTo`](thm.html#ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_igusaTo) and [`ModularCurve.IgusaScheme.geometricallyConnected_toBase_int`](thm.html#ModularCurve.IgusaScheme.geometricallyConnected_toBase_int), and is used in [`ModularCurve.DRModelPackageLevel.bijective_algebraMap_sections_baseChange`](thm.html#ModularCurve.DRModelPackageLevel.bijective_algebraMap_sections_baseChange) to identify the global sections of the model after base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_connectedSpace_pullback_igusaTo_specMap.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem ModularCurve.IgusaScheme.connectedSpace_pullback_igusaTo_specMap
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) L] :
    ConnectedSpace ↥(pullback (igusaTo N ℓ)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt ℓ) L)) := by sorry
