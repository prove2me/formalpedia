-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_residue
-- name    : ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/c6544d22-de76-5953-bccf-613ece227ef9
-- title:
--   Smoothness of the Igusa model's fibre at ℓ ∤ N
-- statement:
--   Fix a level $N \ge 1$ (nonzero as a natural number) and a prime $\ell$ with $\ell \nmid N$, and write $\mathbb{Z}_{(\ell)}$ for [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Let $k$ be an algebraically closed field of characteristic $\ell$ and let $\varphi : \mathbb{Z}_{(\ell)} \to k$ be a ring homomorphism. Let [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) be the scheme obtained as the pushout of the two morphisms $\mathrm{fFin}$ and $\mathrm{fInf}$ from `XMid N ℓ` to the charts `XFin N ℓ` and `XInf N ℓ`, that is, the gluing of the spectra of the two chart algebras $\mathrm{chartAlgFin}_{N,\ell}$ (adjoining $j$) and $\mathrm{chartAlgInf}_{N,\ell}$ (adjoining $j^{-1}$) inside the full modular function field of level $N$, and let `igusaTo N ℓ` be the morphism to $\operatorname{Spec} \mathbb{Z}_{(\ell)}$ induced on the pushout by the two chart structure morphisms. Then the second projection of the fibre product of `igusaTo N ℓ` with $\operatorname{Spec}(\varphi) : \operatorname{Spec} k \to \operatorname{Spec}\mathbb{Z}_{(\ell)}$, namely the base-changed scheme over $\operatorname{Spec} k$, is smooth of relative dimension $1$.
--
--   This is Igusa's good-reduction theorem in the form needed for the Igusa model: for $\ell \nmid N$ the fibre of the model over a characteristic-$\ell$ algebraically closed field is a smooth curve. It is the arithmetic input to the smoothness of the Deligne–Rapoport level models, and is used in the construction of the degeneracy and specialisation data for those models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_residue.lean

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

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_residue
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [CharP k ℓ] [IsAlgClosed k]
    (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k) :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by sorry
