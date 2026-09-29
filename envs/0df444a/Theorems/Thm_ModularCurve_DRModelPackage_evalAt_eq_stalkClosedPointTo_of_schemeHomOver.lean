-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver
-- name    : ModularCurve.DRModelPackage.evalAt_eq_stalkClosedPointTo_of_schemeHomOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/49f92c78-1d8d-52ed-be1e-e84af6cc4ce9
-- title:
--   Germ readings are V-integral with value the section pull-back
-- statement:
--   Fix a prime $p$ with $5 \le p$ and a package $\mathfrak{X} : \mathrm{DRModelPackage}\ p$, whose geometric generic-fibre curve model $M_\eta$ over $\overline{\mathbb{Q}}$ with function field $\mathrm{modularFunctionFieldBar}\ p$ is identified with the $\overline{\mathbb{Q}}$-base change of `DRModel p` by the isomorphism $e_\eta$. Assume, on the preimage of the image of the finite chart $\mathrm{Spec}$ of $\mathrm{chartAlgFin}\ \mathbb{Z}\ (\mathrm{modularFunctionFieldFull}\ p)\ (\mathrm{jFull}\ p)$ (assumed nonempty), the pin $h_{M_\eta}$: for every $a$ in that chart algebra, the element of $\mathrm{modularFunctionFieldBar}\ p$ obtained from the germ of $a$ via $M_\eta.\mathrm{ffEquiv}^{-1}$ has Laurent expansion $\mathrm{coeffEmb}$ of the expansion of $a$. Let $O$ be a discrete valuation domain with maximal ideal $(p)$, $K$ its fraction field, $\iota_K : K \to \overline{\mathbb{Q}}$ a ring homomorphism, and suppose the base change $\mathfrak{X}_O$ of `DRModel p` to $O$ is an integral scheme. Let $x \in \mathfrak{X}_O$, and let $\varphi$ be a ring homomorphism from the function field of $\mathfrak{X}_O$ to $\mathrm{modularFunctionFieldBar}\ (1 \cdot p)$, pinned on constants ($\varphi$ sends the germ at $x$ of $a \in O$ to $\iota_K(a)$) and on the finite chart ($\varphi$ of the germ of $a$ has Laurent expansion $\mathrm{coeffEmb}$ of that of $a$), the relevant chart preimage being nonempty. Further data: a valuation subring $A \subset \overline{\mathbb{Q}}$, a perfect field $k$ of characteristic $p$, $\mathrm{red} : A \to k$, modular polynomial data with Kronecker congruence, integrality of the Hecke maps $\bar\alpha, \bar\beta$ at level $1, p$, a place specialisation $P$ and a prolongation tuple $R$ for it. Let $e_{\mathrm{Pl}}$ be a bijection between places of $\mathrm{modularFunctionFieldBar}\ (1 \cdot p)$ and of $\mathrm{modularFunctionFieldBar}\ p$ over $\overline{\mathbb{Q}}$ which, on elements with equal Laurent expansions, preserves membership in the valuation subring and the value of $\mathrm{evalAt}$. Let $V$ be a place of $\mathrm{modularFunctionFieldBar}\ (1 \cdot p)$ and let $t$ be a section of $\mathfrak{X}_O \to \mathrm{Spec}\ O$ such that: composing $\mathrm{Spec}$ of $\iota_K \circ (O \to K)$ with $t$ and with the projection to `DRModel p` gives the $\overline{\mathbb{Q}}$-point of $M_\eta$ attached by $M_\eta.\mathrm{pointEquivPlace}$ to $e_{\mathrm{Pl}}(V)$, composed with $e_\eta$ and the projection; the closed point of $\mathrm{Spec}\ O$ maps to $x$; and $x$ lies in the finite-chart preimage. Then for every germ $s$ of $\mathfrak{X}_O$ at $t(\text{closed point})$, the image $\varphi(s)$ of $s$ in $\mathrm{modularFunctionFieldBar}\ (1 \cdot p)$ (through the stalk identification along $hx$ and the map to the function field) lies in the valuation subring of $V$, and $V.\mathrm{evalAt}(\varphi(s)) = \iota_K$ of the image in $K$ of $t^{*}s \in O$, the pull-back of $s$ along $t$ to the stalk at the closed point.
--
--   This is the evaluation-matching step for the Deligne–Rapoport integral model: it identifies the value at a place $V$ of the reading of a germ with the pull-back of that germ along the $\mathcal{O}$-section passing through the given point, so that place-theoretic values and sections of the integral model compute the same element of $\overline{\mathbb{Q}}$. It is used in the analysis of chart presentations and branches at a point of the model, in the comparison of orders of vanishing with section pull-backs, and in the identification of widths of components on the resolved model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_evalAt_eq_stalkClosedPointTo_of_schemeHomOver.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.DRModelPackage.evalAt_eq_stalkClosedPointTo_of_schemeHomOver
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))

    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
          (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
    (t : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O)))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (ht : Spec.map (CommRingCat.ofHom (ιK.comp (algebraMap O K))) ≫ t.1 ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      (𝔛.Mη.pointEquivPlace.symm (ePl V)).1 ≫ 𝔛.eη ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))))
    (hx : t.1.base (IsLocalRing.closedPoint O) = x)
    (hfin : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
    (s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
      (t.1.base (IsLocalRing.closedPoint O))) :
    φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
          (.of_eq hx) |>.hom.hom s)) ∈ V.toValuationSubring ∧
    V.evalAt (φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
          (.of_eq hx) |>.hom.hom s))) =
      ιK (algebraMap O K (Scheme.stalkClosedPointTo t.1 s)) := by sorry
