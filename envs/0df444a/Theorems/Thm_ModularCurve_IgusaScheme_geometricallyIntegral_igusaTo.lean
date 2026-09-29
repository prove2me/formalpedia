-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_geometricallyIntegral_igusaTo
-- name    : ModularCurve.IgusaScheme.geometricallyIntegral_igusaTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/8f01873d-f7e9-5f76-8b8e-8aefb9dcaedb
-- title:
--   Geometric integrality of the Igusa scheme over ℤ_{(ℓ)}
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $\ell$ with $\ell \nmid N$, and write $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the localisation of $\mathbb{Q}$ at $\ell$ used throughout the project. Inside the field $F =$ `modularFunctionFieldFull N` one has the two $\mathbb{Z}_{(\ell)}$-subalgebras `chartAlgFin N ℓ` $=$ `chartAlg N ℓ {jFull N}` and `chartAlgInf N ℓ` $=$ `chartAlg N ℓ {(jFull N)⁻¹}`, the charts attached to the modular function $j$ and to $j^{-1}$ respectively. The Igusa scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout in schemes of the two morphisms `fFin N ℓ : XMid N ℓ ⟶ XFin N ℓ` and `fInf N ℓ : XMid N ℓ ⟶ XInf N ℓ` obtained by applying `Spec` to the ring maps `inclFin N ℓ` and `inclInf N ℓ`, i.e. the gluing of the two charts along their common overlap, and `igusaTo N ℓ` is the morphism from this pushout to $\operatorname{Spec} \mathbb{Z}_{(\ell)}$ determined by the universal property from the structure morphisms of the two charts as $\mathbb{Z}_{(\ell)}$-algebras. The theorem asserts `GeometricallyIntegral (igusaTo N ℓ)`: this morphism is geometrically integral, so that after base change along any field-valued point of the base the resulting scheme is integral; in particular each geometric fibre, over $\overline{\mathbb{Q}}$ and over $\overline{\mathbb{F}_\ell}$, is an integral scheme.
--
--   This is the statement that the Igusa model of the modular curve of level $N$ over $\mathbb{Z}_{(\ell)}$, for $\ell$ prime to the level, has integral generic and special geometric fibres; it is the geometric-integrality input for the Deligne–Rapoport style model package, and is used by the level-model lemmas [`ModularCurve.DRModelPackageLevel.baseChangeSnd_comp_comp`](thm.html#ModularCurve.DRModelPackageLevel.baseChangeSnd_comp_comp), [`ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel`](thm.html#ModularCurve.DRModelPackageLevel.exists_torusFibre_abqFibre_degeneracy_specialFibre_pins_of_levelModel) and [`ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq`](thm.html#ModularCurve.DRModelPackageLevel.isReduced_pullback_ker_fibreRestrictAlong_normHom_of_comp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_geometricallyIntegral_igusaTo.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.geometricallyIntegral_igusaTo
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    GeometricallyIntegral (igusaTo N ℓ) := by sorry
