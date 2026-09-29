-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat
-- name    : ModularCurve.IgusaScheme.exists_curveModel_genericFibre_iso_and_galoisCompat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/d5a3f8ee-3539-5302-89e4-9c4de72e36bc
-- title:
--   Geometric generic fibre of the Igusa scheme as a curve model
-- statement:
--   Let $N\ge 1$, let $\ell$ be a prime with $\ell\nmid N$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $\ell$. The assertion is the existence of the following data. First, a `CurveModel` $M_\eta$ over $K=\overline{\mathbb{Q}}$ (an `AlgebraicClosure ℚ`) with field $L=$ `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ inside $\overline{\mathbb{Q}}((q))$ of the intermediate field `modularFunctionFieldFull N` of $\mathbb{Q}((q))$: that is, an integral scheme $M_\eta.C$ with a proper, smooth of relative dimension $1$ morphism $M_\eta.\mathrm{toBase}$ to $\operatorname{Spec} K$, a ring isomorphism $L\simeq$ the function field of $M_\eta.C$ compatible with the structure map from $K$, a bijection from the closed points of $M_\eta.C$ to the places of $L/K$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open. Second, a morphism $e_\eta$ from $M_\eta.C$ to the fibre product of `igusaTo N ℓ` (the structure morphism of [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255), the pushout of `fFin N ℓ` and `fInf N ℓ`, over $\operatorname{Spec}\mathbb{Z}_{(\ell)}$) with $\operatorname{Spec}$ of $\mathbb{Z}_{(\ell)}\to\overline{\mathbb{Q}}$, which is an isomorphism and satisfies $e_\eta$ followed by the second projection $=M_\eta.\mathrm{toBase}$. Third, Galois compatibility: for every $g\in\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all sections $x,x'$ of $M_\eta.\mathrm{toBase}$ (morphisms $\operatorname{Spec}\overline{\mathbb{Q}}\to M_\eta.C$ composing with $M_\eta.\mathrm{toBase}$ to the identity), if the image of $x'$ in the Igusa scheme under $e_\eta$ followed by the first projection equals $\operatorname{Spec}(g)$ followed by that of $x$, then $M_\eta.\mathrm{pointEquivPlace}\,x'$ equals the translate of $M_\eta.\mathrm{pointEquivPlace}\,x$ by the semilinear automorphism $\mathrm{arithmeticGalois}(\mathtt{modularFunctionFieldFull }N)(g)$, where $\mathrm{pointEquivPlace}$ is the composite bijection from such sections to closed points and then to places of $L/K$.
--
--   This identifies the geometric generic fibre of Igusa's $\mathbb{Z}_{(\ell)}$-model of $X_0(N)$ with a curve model of the function field $\overline{\mathbb{Q}}(X_0(N))$, together with the equivariance of the place–point dictionary for the action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $q$-expansions. It feeds [`ModularCurve.IgusaScheme.isProper_and_smooth_and_geometricallyIntegral`](thm.html#ModularCurve.IgusaScheme.isProper_and_smooth_and_geometricallyIntegral), where properness, smoothness and geometric integrality of the Igusa scheme over $\mathbb{Z}_{(\ell)}$ are deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_curveModel_genericFibre_iso_and_galoisCompat.lean

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

theorem ModularCurve.IgusaScheme.exists_curveModel_genericFibre_iso_and_galoisCompat
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N) :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (eη : Mη.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) (_ : IsIso eη),
      eη ≫ pullback.snd (igusaTo N ℓ) _ = Mη.toBase ∧
      ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst (igusaTo N ℓ) _ →
        Mη.pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g •
            Mη.pointEquivPlace x := by sorry
