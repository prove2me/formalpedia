-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal_swap
-- name    : ModularCurve.DRModelPackage.phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/a875b515-6ac9-5163-9ca4-e14b71dcd0a3
-- title:
--   Branch integrality and j-attainment at a supersingular crossing (exchanged labels)
-- statement:
--   Fix a prime $p\ge 5$ and a `DRModelPackage p` $\mathfrak X$, the bundled data of the two-chart integral model `DRModel p` of `modularFunctionFieldFull p` over $\mathbb Z$ (properness, flatness and integrality of `DRModel.toBase p`, normality on affine opens, curve models over $\mathbb Q$ and $\overline{\mathbb Q}$, sections, a smooth locus, and the component morphisms $\mathfrak X.\mathrm{compZero}\,k,\ \mathfrak X.\mathrm{compInf}\,k$ from $(\mathfrak X.\mathrm{ratModel}\,k).C$ into the base change of the model to $k$). Let $O$ be a discrete valuation domain with $\mathfrak m_O=(p)$, $K$ its fraction field and $\iota_K:K\to\overline{\mathbb Q}$ a ring homomorphism. Write $X_O$ for the base change of `DRModel.toBase p` along $\operatorname{Spec}O\to\operatorname{Spec}\mathbb Z$, assumed integral, let $x\in X_O$ and let $\varphi$ be a ring homomorphism from the function field of $X_O$ into `modularFunctionFieldBar (1 * p)`, the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of `modularFunctionFieldFull p`. It is assumed that $\varphi$ carries the germ at $x$ of the global section coming from $a\in O$ to $\iota_K(a)$ (hypothesis `hφO`), that the preimage of the finite chart under `pullback.fst` is nonempty, and that $\varphi$ carries the germ of $a$ in the finite chart algebra `chartAlgFin ℤ (modularFunctionFieldFull p) (IgusaScheme.jFull p)` (the integral closure of $\mathbb Z[j]$) to the coefficient extension of $a$ (hypothesis `hφj`). Further data: a valuation subring $A\subseteq\overline{\mathbb Q}$, an algebraically closed perfect field $k$ of characteristic $p$, $\mathrm{red}:A\to k$, modular polynomial data for $p$ satisfying the Kronecker congruence $\Phi\equiv(X'^p-X)(X'-X^p)\bmod p$, integrality of the two level-raising maps $\bar\alpha,\bar\beta$ at level $(1,p)$, a `PlaceSpecialization` $P$ and a `ProlongationTuple` $R$ over it, with $\iota_K(O)\subseteq A$ and $\mathrm{to}\kappa:O\to k$ inducing $\mathrm{red}\circ\iota_K$; a place $w$ of `modularFunctionFieldC k 1` in the supersingular set `ssPlaces p 1 k`; an element $\hat\jmath\in O$ whose reduction is $w(\,j\,)$ together with an element of $\mathfrak m_{\mathcal O_{X_O,x}}$ mapping under $\varphi$ to $j-\iota_K(\hat\jmath)$; a point $n$ of the fibre product of $\mathfrak X.\mathrm{compInf}\,k$ and $\mathfrak X.\mathrm{compZero}\,k$ whose two images in $(\mathfrak X.\mathrm{ratModel}\,k).C$ are closed and both map to $x$ after composing with `DRModel.baseChangeMap toκ`, the images $\xi_1,\xi_2$ of the generic point of $(\mathfrak X.\mathrm{ratModel}\,k).C$ under $\mathfrak X.\mathrm{compZero}\,k$ and $\mathfrak X.\mathrm{compInf}\,k$ followed by `DRModel.baseChangeMap toκ` specialising to $x$; a stalk element $t_F$ at $x$ with $\varphi(t_F)=j(q^p)-j(q)^p$ whose image in the stalk at $\xi_1$ lies in the maximal ideal; and the assumption that $\varphi$ maps every germ at $x$ into $R.\mathrm{nodeIntegers}\,w$, i.e. into $R_1\cap R_2$ and into every place $V$ of `modularFunctionFieldBar (1 * p)` with $P.\mathrm{reduceFst}\,V=w$. The conclusion asserts four things: $\varphi$ maps the stalk at $\xi_1$ into $R.R_1.\mathrm{integers}$ and its maximal ideal into the nonunits thereof; $\varphi$ maps the stalk at $\xi_2$ into $R.R_2.\mathrm{integers}$ and its maximal ideal into the nonunits thereof; some germ at $\xi_1$ has $\varphi$-image $j=\mathrm{jFun}\,1\,p$; and some germ at $\xi_2$ has $\varphi$-image $j(q^p)=\mathrm{jQFun}\,1\,p$.
--
--   This is the oriented identification of the two branch local rings of the Deligne–Rapoport model at a supersingular crossing with the two regular prolongations $R_1,R_2$ of the prolongation tuple, in the labelling where the branch carrying the orientation datum (vanishing of $j(q^p)-j(q)^p$) is the one cut out by $\mathfrak X.\mathrm{compZero}$ and is matched with $R_1$. It is used by [`ModularCurve.DRModelPackage.nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal_swap`](thm.html#ModularCurve.DRModelPackage.nodeResidue_eq_zero_iff_and_ord_eq_of_specializes_of_mem_maximalIdeal_swap), which computes residues and orders of vanishing along the two branches.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal_swap.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization
open Classical in

theorem ModularCurve.DRModelPackage.phi_algebraMap_stalk_mem_integers_and_exists_eq_jFun_of_specializes_of_mem_maximalIdeal_swap
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)

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
    {k : Type} [Field k] [CharP k p] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ) (R : ProlongationTuple P)
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)

    [IsAlgClosed k] (toκ : O →+* k) (htoκ : ∀ a : O, toκ a = red ⟨ιK (algebraMap O K a), hιA a⟩)

    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ ssPlaces p 1 k)
    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (htF : φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField tF) =
      ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p)
    (hor : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom tF ∈ IsLocalRing.maximalIdeal _)

    (hconv : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x, φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField s) ∈ R.nodeIntegers w) :

    (∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₁.integers ∧
        (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₁.integers.nonunits)) ∧

    (∀ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₂.integers ∧
        (u ∈ IsLocalRing.maximalIdeal _ → φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) ∈ R.R₂.integers.nonunits)) ∧

    (∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) = ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) ∧
    (∃ u : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)),
      φ (algebraMap _ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) u) = ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p) := by sorry
