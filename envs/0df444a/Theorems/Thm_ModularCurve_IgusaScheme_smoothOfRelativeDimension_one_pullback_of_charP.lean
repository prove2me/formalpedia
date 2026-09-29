-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_charP
-- name    : ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/5ec8ebed-5621-59c5-a5ef-1b4eaddf4f76
-- title:
--   Smoothness of the Igusa scheme over characteristic-ℓ fields
-- statement:
--   Let $N$ be a nonzero natural number, $\ell$ a prime not dividing $N$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of those rationals whose denominator is coprime to $\ell$. Let $k$ be a field of characteristic $\ell$ and let $\varphi \colon \mathbb{Z}_{(\ell)} \to k$ be a ring homomorphism. The scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) is the pushout, in schemes, of the two morphisms $\mathrm{Spec}$ of the inclusions of the middle algebra into the chart algebras `chartAlgFin N ℓ` and `chartAlgInf N ℓ` — the $\mathbb{Z}_{(\ell)}$-subalgebras of the full modular function field of level $N$ given by `chartAlg N ℓ` applied to $\{j\}$ and to $\{j^{-1}\}$ — and `igusaTo N ℓ` is the morphism to $\mathrm{Spec}\,\mathbb{Z}_{(\ell)}$ obtained from the two structure morphisms by the pushout property. The assertion is that the second projection of the fibre product of `igusaTo N ℓ` with $\mathrm{Spec}(\varphi)$, that is the base change of the Igusa scheme along $\varphi$ viewed as a $k$-scheme, is smooth of relative dimension $1$ over $\mathrm{Spec}\,k$.
--
--   This is the form of Igusa's smoothness theorem for the $\ell$-integral model of the modular curve of level $N$ with $\ell \nmid N$, stated for an arbitrary characteristic-$\ell$ base field rather than only for algebraically closed ones. It is used in the construction of the Deligne–Rapoport model package, where fibres of the Igusa scheme over residue fields and over geometric points are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_charP.lean

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

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_charP
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (k : Type) [Field k] [CharP k ℓ]
    (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k) :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by sorry
