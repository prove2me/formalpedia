-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf
-- name    : ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/c30b37b8-443a-547d-b305-2134bbc66023
-- title:
--   Smoothness of the Igusa fibre from its two charts
-- statement:
--   Fix a level $N \ge 1$ and a prime $\ell$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $\ell$. Let $k$ be a field and $\varphi \colon \mathbb{Z}_{(\ell)} \to k$ a ring homomorphism. Inside the modular function field $F$ of full level $N$ consider the two chart algebras over $\mathbb{Z}_{(\ell)}$: `chartAlgFin N ℓ`, the elements of $F$ integral over $\mathbb{Z}_{(\ell)}[j]$, and `chartAlgInf N ℓ`, the elements integral over $\mathbb{Z}_{(\ell)}[j^{-1}]$, where $j$ is the modular $j$-function viewed in $F$. Assume that the base change along $\operatorname{Spec}\varphi$ of each structure morphism $\operatorname{Spec}(\text{chart}) \to \operatorname{Spec}\mathbb{Z}_{(\ell)}$ — that is, the second projection of the pullback of $\operatorname{Spec}$ of the algebra map with $\operatorname{Spec}\varphi$ — is smooth of relative dimension $1$, for the finite chart (hypothesis `hFin`) and for the chart at infinity (hypothesis `hInf`). The conclusion is that the base change along $\operatorname{Spec}\varphi$ of `igusaTo N ℓ`, the morphism from the Igusa scheme [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255) (the pushout of the two charts along the middle scheme `XMid N ℓ`) to $\operatorname{Spec}\mathbb{Z}_{(\ell)}$ induced by the two algebra maps, is again smooth of relative dimension $1$.
--
--   This is the Zariski gluing step for the Igusa scheme: smoothness of relative dimension $1$ over a base field is local on the source, so it descends from the two affine charts covering the Igusa scheme to the whole fibre. It is used by the statements treating the fibre in characteristic zero and the fibre at the residue characteristic, where the per-chart smoothness is supplied by the arithmetic input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf.lean

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

theorem ModularCurve.IgusaScheme.smoothOfRelativeDimension_one_pullback_of_chartFin_of_chartInf
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type) [Field k] (φ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* k)
    (hFin : SmoothOfRelativeDimension 1
      (pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgFin N ℓ))))
        (Spec.map (CommRingCat.ofHom φ))))
    (hInf : SmoothOfRelativeDimension 1
      (pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ))))
        (Spec.map (CommRingCat.ofHom φ)))) :
    SmoothOfRelativeDimension 1
      (pullback.snd (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom φ))) := by sorry
