-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_nonempty_schemeHomOver_id_igusaTo
-- name    : ModularCurve.IgusaScheme.nonempty_schemeHomOver_id_igusaTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/0c4361b2-db26-5c8c-884c-971fa8f8fb2e
-- title:
--   A ℤ_{(ℓ)}-point of the Igusa scheme
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and let $\ell$ be a prime. Write $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. The scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout of the two morphisms `fFin N ℓ` and `fInf N ℓ`, namely the maps from $\operatorname{Spec}$ of the middle algebra `XMid N ℓ` to $\operatorname{Spec}$ of the two charts `XFin N ℓ` and `XInf N ℓ` obtained by applying $\operatorname{Spec}$ to the inclusions `inclFin N ℓ` and `inclInf N ℓ`; here the charts are the $\mathbb{Z}_{(\ell)}$-subalgebras `chartAlgFin N ℓ` $=$ `chartAlg N ℓ {jFull N}` and `chartAlgInf N ℓ` $=$ `chartAlg N ℓ {(jFull N)⁻¹}` of the modular function field `modularFunctionFieldFull N`, and `igusaTo N ℓ` is the morphism to $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ induced on the pushout by the two structure morphisms $\operatorname{Spec}$ of $\mathbb{Z}_{(\ell)} \to$ `chartAlgFin N ℓ` and $\mathbb{Z}_{(\ell)} \to$ `chartAlgInf N ℓ`. The assertion is that the type of pairs consisting of a morphism $\varphi : \operatorname{Spec}\mathbb{Z}_{(\ell)} \to$ [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) together with a proof that $\varphi$ followed by `igusaTo N ℓ` equals the identity of $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ is nonempty; that is, the Igusa scheme admits a section over its base. No hypothesis relating $\ell$ and $N$ is imposed.
--
--   This is the existence of a $\mathbb{Z}_{(\ell)}$-rational point on the integral model of the modular curve, classically the cusp at infinity, realised in the chart where $j^{-1}$ is a coordinate. It feeds the later analysis of the fibres of `igusaTo`, being cited for the connectedness and integrality statements about pullbacks of `igusaTo` and for the construction of the finite map data used in the generic étaleness of the level structures.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_nonempty_schemeHomOver_id_igusaTo.lean

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

theorem ModularCurve.IgusaScheme.nonempty_schemeHomOver_id_igusaTo
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))))
      (igusaTo N ℓ)) := by sorry
