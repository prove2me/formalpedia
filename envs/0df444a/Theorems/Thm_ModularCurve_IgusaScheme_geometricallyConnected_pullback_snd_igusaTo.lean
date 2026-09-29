-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_igusaTo
-- name    : ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_igusaTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/a43c110d-2c3b-5ab2-a2ad-ea4abd5a6289
-- title:
--   Fibres of the Igusa scheme are geometrically connected
-- statement:
--   Fix $N \geq 1$ and a prime $\ell$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Inside the field $F$ of full modular functions of level $N$, let `chartAlgFin N ℓ` be the $\mathbb{Z}_{(\ell)}$-subalgebra of elements integral over $\mathbb{Z}_{(\ell)}[j]$ and `chartAlgInf N ℓ` the subalgebra of elements integral over $\mathbb{Z}_{(\ell)}[j^{-1}]$, where $j$ is the modular invariant viewed in $F$; both are assumed to be of finite type over $\mathbb{Z}_{(\ell)}$. The Igusa scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout of the two affine charts $\operatorname{Spec}$ `chartAlgFin N ℓ` and $\operatorname{Spec}$ `chartAlgInf N ℓ` along their common overlap, and `igusaTo N ℓ` is the morphism to $\operatorname{Spec} \mathbb{Z}_{(\ell)}$ obtained by descending the two structure morphisms through the pushout. The assertion is: for every field $K$ and every ring homomorphism $\varphi \colon \mathbb{Z}_{(\ell)} \to K$, the second projection of the fibre product of `igusaTo N ℓ` with $\operatorname{Spec} \varphi$, i.e. the base-changed morphism to $\operatorname{Spec} K$, is geometrically connected.
--
--   This is the geometric connectedness of all fibres of the Igusa model over $\operatorname{Spec}\mathbb{Z}_{(\ell)}$, classically a consequence of Zariski's connectedness theorem (or Stein factorisation) applied to the proper flat structure morphism with integral total space over a connected base. It is used in establishing that the fibres of `igusaTo` are integral, and more generally in verifying the axioms for the Igusa scheme as a relative curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_geometricallyConnected_pullback_snd_igusaTo.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  ModularCurve AlgebraicCurve ModularCurve.IgusaScheme ModularCurve.CharPModel

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.geometricallyConnected_pullback_snd_igusaTo
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ)]
    [Algebra.FiniteType ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)]
    (K : Type) [Field K] (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* K) :
    GeometricallyConnected (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by sorry
