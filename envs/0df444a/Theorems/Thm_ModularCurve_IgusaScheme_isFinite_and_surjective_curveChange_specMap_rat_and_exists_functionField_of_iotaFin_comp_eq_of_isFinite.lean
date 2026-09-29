-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_isFinite_and_surjective_curveChange_specMap_rat_and_exists_functionField_of_iotaFin_comp_eq_of_isFinite
-- name    : ModularCurve.IgusaScheme.isFinite_and_surjective_curveChange_specMap_rat_and_exists_functionField_of_iotaFin_comp_eq_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/28b006c5-4bac-50e2-a699-1b47714c7634
-- title:
--   Pinned Igusa morphism: finite, surjective generic fibre and degree
-- statement:
--   Fix natural numbers $M,M'\ge 1$ and a prime $q$, and write $R\,q$ for the base ring [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8) (a subring of $\mathbb Q$ of which $\mathbb Q$ is the fraction field). Recall that `IgusaScheme N q` is the pushout gluing $\operatorname{Spec}$ of the two chart algebras `chartAlgFin N q` and `chartAlgInf N q` — the $R\,q$-subalgebras of integral elements over $R\,q[j]$, resp. $R\,q[j^{-1}]$, inside $F_N :=$ `modularFunctionFieldFull N`, the subfield of $\mathbb Q(\!(q)\!)$ generated over $\mathbb Q$ by the expansions $j(q^d)$ for $0\neq d\mid N$ — with structure morphism `igusaTo N q` to $\operatorname{Spec}(R\,q)$. The data are: a morphism $\pi$ from `IgusaScheme M' q` to `IgusaScheme M q` over $\operatorname{Spec}(R\,q)$ (i.e. $\pi_1$ followed by `igusaTo M q` is `igusaTo M' q`); an $R\,q$-algebra map $\iota$ from `chartAlgFin M q` to `chartAlgFin M' q`; a ring endomorphism $e$ of $\mathbb Q(\!(q)\!)$ such that $\iota$ computes $e$ on Laurent expansions ($hι$) and $e$ maps $F_M$ into $F_{M'}$ ($he$); the pinning condition that the $j$-finite chart inclusion `ιFin M' q` followed by $\pi_1$ equals $\operatorname{Spec}\iota$ followed by `ιFin M q`; finiteness of $\operatorname{Spec}\iota$; and integrality of both $\mathbb Q$-fibres $\operatorname{pullback}(\mathrm{igusaTo}\,N\,q,\ \operatorname{Spec}(R\,q\to\mathbb Q))$ for $N=M,M'$. The conclusion asserts that the base change $\pi_{\mathbb Q} :=$ `curveChange π.1 π.2 (specMap (R q) ℚ)` between these $\mathbb Q$-fibres is finite and surjective, and that there exist a nonempty affine open $U$ of the fibre $Y$ of level $M$ and a ring homomorphism $\varphi : F_M \to F_{M'}$ inducing $e$ on $q$-expansions, such that, with $\Gamma(X,\pi_{\mathbb Q}^{-1}U)$ made a $\Gamma(Y,U)$-algebra via $\pi_{\mathbb Q}$, one has $\dim_{K(Y)}\bigl(K(Y)\otimes_{\Gamma(Y,U)}\Gamma(X,\pi_{\mathbb Q}^{-1}U)\bigr) = \dim_{F_M} F_{M'}$, the latter rank taken for the $F_M$-module structure on $F_{M'}$ given by $\varphi$.
--
--   This is the generic-fibre comparison for a morphism of Igusa schemes of two arbitrary levels which is pinned on the $j$-finite chart by a finite map of chart algebras: it converts the chart-level data $(\iota,e)$ into finiteness and surjectivity of the morphism of curves over $\mathbb Q$ together with an identification of its generic degree with the degree of the corresponding extension of modular function fields. It is used for the degeneracy and forgetful morphisms of the Deligne–Rapoport model package, being cited by [`ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat), [`ModularCurve.DRModelPackageLevel.finrank_pi_eq`](thm.html#ModularCurve.DRModelPackageLevel.finrank_pi_eq) and [`ModularCurve.IgusaScheme.finrank_eq_of_pinned_of_flat_morphismRestrict`](thm.html#ModularCurve.IgusaScheme.finrank_eq_of_pinned_of_flat_morphismRestrict).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_isFinite_and_surjective_curveChange_specMap_rat_and_exists_functionField_of_iotaFin_comp_eq_of_isFinite.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct AlgebraicGeometry ModularCurve ModularCurve.DRLevel AlgebraicGeometry.SmoothProperCurve
  AlgebraicGeometry.RelPicard NeronModelInfra

theorem ModularCurve.IgusaScheme.isFinite_and_surjective_curveChange_specMap_rat_and_exists_functionField_of_iotaFin_comp_eq_of_isFinite
    (M M' q : ℕ) [NeZero M] [NeZero M'] [Fact q.Prime]
    (π : SchemeHomOver (IgusaScheme.igusaTo M' q) (IgusaScheme.igusaTo M q))
    (ι : ↥(IgusaScheme.chartAlgFin M q) →ₐ[R q] ↥(IgusaScheme.chartAlgFin M' q))
    (e : LaurentSeries ℚ →+* LaurentSeries ℚ)
    (hι : ∀ b : ↥(IgusaScheme.chartAlgFin M q),
      (((ι b : ↥(IgusaScheme.chartAlgFin M' q)) : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) =
        e ((b : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ))
    (he : ∀ f : ↥(modularFunctionFieldFull M),
      e (f : LaurentSeries ℚ) ∈ modularFunctionFieldFull M')
    (hπ : IgusaScheme.ιFin M' q ≫ π.1 = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ IgusaScheme.ιFin M q)
    (hιfin : IsFinite (Spec.map (CommRingCat.ofHom ι.toRingHom)))
    [IsIntegral (pullback (IgusaScheme.igusaTo M' q) (specMap (R q) ℚ))] [IsIntegral (pullback (IgusaScheme.igusaTo M q) (specMap (R q) ℚ))] :
    IsFinite (curveChange π.1 π.2 (specMap (R q) ℚ)) ∧ Surjective (curveChange π.1 π.2 (specMap (R q) ℚ)) ∧
    ∃ (U : (pullback (IgusaScheme.igusaTo M q) (specMap (R q) ℚ)).Opens) (_ : IsAffineOpen U) (_ : Nonempty (U : Scheme.{0}))
      (φ : ↥(modularFunctionFieldFull M) →+* ↥(modularFunctionFieldFull M')),
      (∀ f : ↥(modularFunctionFieldFull M),
        ((φ f : ↥(modularFunctionFieldFull M')) : LaurentSeries ℚ) = e ((f : ↥(modularFunctionFieldFull M)) : LaurentSeries ℚ)) ∧
      (letI : Algebra Γ(pullback (IgusaScheme.igusaTo M q) (specMap (R q) ℚ), U)
          Γ(pullback (IgusaScheme.igusaTo M' q) (specMap (R q) ℚ), (curveChange π.1 π.2 (specMap (R q) ℚ)) ⁻¹ᵁ U) :=
        ((curveChange π.1 π.2 (specMap (R q) ℚ)).appLE U ((curveChange π.1 π.2 (specMap (R q) ℚ)) ⁻¹ᵁ U) le_rfl).hom.toAlgebra
       Module.finrank (pullback (IgusaScheme.igusaTo M q) (specMap (R q) ℚ)).functionField
           ((pullback (IgusaScheme.igusaTo M q) (specMap (R q) ℚ)).functionField ⊗[Γ(pullback (IgusaScheme.igusaTo M q) (specMap (R q) ℚ), U)]
             Γ(pullback (IgusaScheme.igusaTo M' q) (specMap (R q) ℚ), (curveChange π.1 π.2 (specMap (R q) ℚ)) ⁻¹ᵁ U)) =
         @Module.finrank ↥(modularFunctionFieldFull M) ↥(modularFunctionFieldFull M') _ _ φ.toAlgebra.toModule) := by sorry
