-- Prove2me | Theorems.Thm_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom
-- name    : ModularCurve.exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0bddf70f-8eb5-53fb-ac7b-518dc56ac8e5
-- title:
--   Models of X₁(M) over ℚ̄ and k, with place reduction
-- statement:
--   Throughout, $\mathbb Z_{(p)}$ denotes the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb Q$ consisting of the rationals whose denominator is coprime to $p$, and $F_1$ denotes [`ModularCurve.x1FunctionField M`](def/ModularCurve_X1.html#L137), that is [`ModularCurve.x1FunctionFieldC ℚ M = ModularCurve.qExpFunctionFieldC ℚ (Gamma1 M)`](def/ModularCurve_X1.html#L134): the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by `intFormRatiosC ℚ (Gamma1 M)`. For a field $L$ of characteristic $0$ with $\mathbb Q$-algebra structure, [`ModularCurve.laurentBaseChange L F₀`](def/ModularCurve_LaurentCoeff.html#L103) is the subfield of $L((q))$ generated over $L$ by the coefficientwise image [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of $F_0$; write $\mathcal F =$ [`ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) F₁`](def/ModularCurve_LaurentCoeff.html#L103). A `Place K F` is a valuation subring of $F$ containing the image of $K$, distinct from $F$ itself, and a principal ideal ring; `nonunits` of such a ring is its maximal ideal. A `CurveModel K L` consists of an integral scheme $C$ together with a proper, smooth, relative dimension one morphism `toBase : C ⟶ Spec K`, a ring isomorphism of $L$ with the function field of $C$ compatible with the structure map, and a bijection between the closed points of $C$ and the places of $L$ over $K$ matching stalks with valuation subrings, every finite set of points lying in an affine open; `pointEquivPlace` is the resulting bijection between the sections $q : \operatorname{Spec} K \to C$ of `toBase` and the places of $L$ over $K$ when $K$ is algebraically closed. Finally, [`AlgebraicCurve.TwoChartIntegralModel ℤ_{(p)} F₁ j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) is the pushout of the two morphisms `fFin`, `fInf` out of the middle chart, i.e. the scheme obtained by gluing the spectra of the two chart algebras `chartAlgFin` (the elements of $F_1$ integral over $\mathbb Z_{(p)}[j]$) and `chartAlgInf` (the elements integral over $\mathbb Z_{(p)}[j^{-1}]$), with `toBase` the induced morphism to $\operatorname{Spec}\mathbb Z_{(p)}$ and `ιFin`, `ιInf` the two chart morphisms into it.
--
--   The data are: a prime $p$; a natural number $M \neq 0$ with $p \nmid M$; a nonzero element $j$ of $F_1$ whose $q$-expansion is [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the power series `jNum` mapped into $\mathbb Q$; a valuation subring $Pl$ of $\overline{\mathbb Q}$ with `hPl : Pl.LiesOverPrime p`, that is, the image of $p$ in $\overline{\mathbb Q}$ lies in `Pl.nonunits`; an algebraically closed field $k$ of characteristic $p$; and a ring homomorphism $\pi_k : Pl \to k$.
--
--   The assertion is the existence of the following objects and properties.
--
--   (1) A curve model $M_\eta$ of $\mathcal F$ over $\overline{\mathbb Q}$, together with a morphism $e_\eta$ from $M_\eta.C$ to the pullback of [`AlgebraicCurve.TwoChartIntegralModel.toBase ℤ_{(p)} F₁ j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) along $\operatorname{Spec}$ of the inclusion $\mathbb Z_{(p)} \to \overline{\mathbb Q}$, such that $e_\eta$ is an isomorphism and $e_\eta$ followed by the second projection equals $M_\eta$`.toBase`.
--
--   (2) Two chart-centre laws for $M_\eta$. For every section $x$ of $M_\eta$`.toBase` over $\operatorname{Spec}\overline{\mathbb Q}$ and every ring homomorphism $\beta$ from `chartAlgFin ℤ_{(p)} F₁ j` to $\overline{\mathbb Q}$: if $x$ followed by $e_\eta$ followed by the first projection equals $\operatorname{Spec}$ of $\beta$ followed by `ιFin`, then for every $b$ in `chartAlgFin` the element of $\mathcal F$ obtained as the coefficientwise image [`ModularCurve.coeffEmb (AlgebraicClosure ℚ)`](def/ModularCurve_LaurentCoeff.html#L81) of the $q$-expansion of $b$, minus the constant $\beta(b)$, lies in the non-units of the valuation subring of the place $M_\eta$`.pointEquivPlace x`. The same statement holds verbatim with `chartAlgInf` and `ιInf` in place of `chartAlgFin` and `ιFin`.
--
--   (3) Galois equivariance of $M_\eta$: for every $\sigma \in \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and all sections $x, x'$ of $M_\eta$`.toBase`, if the composite of $x'$ with $e_\eta$ and the first projection equals $\operatorname{Spec}$ of $\sigma$ followed by the corresponding composite for $x$, then $M_\eta$`.pointEquivPlace x'` is the translate of $M_\eta$`.pointEquivPlace x` under [`ModularCurve.arithmeticGalois F₁ σ`](def/ModularCurve_ArithmeticGalois.html#L54), the semilinear automorphism of $\mathcal F$ given by the coefficientwise action of $\sigma$ on Laurent series paired with $\sigma$ on constants, acting on places by transport.
--
--   (4) A ring homomorphism $\rho_0 : \mathbb Z_{(p)} \to Pl$ whose composite with the inclusion $Pl \hookrightarrow \overline{\mathbb Q}$ is the structure map $\mathbb Z_{(p)} \to \overline{\mathbb Q}$.
--
--   (5) A curve model $\mathrm{Mdl}$ of [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134) over $k$, together with a morphism $e$ from $\mathrm{Mdl}.C$ to the pullback of [`AlgebraicCurve.TwoChartIntegralModel.toBase ℤ_{(p)} F₁ j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L258) along $\operatorname{Spec}$ of $\pi_k \circ \rho_0$, such that $e$ is an isomorphism and $e$ followed by the second projection equals $\mathrm{Mdl}$`.toBase`.
--
--   (6) Reduction maps on the charts: ring homomorphisms $\pi_{\mathrm{Fin}}$ from `chartAlgFin ℤ_{(p)} F₁ j` and $\pi_{\mathrm{Inf}}$ from `chartAlgInf ℤ_{(p)} F₁ j` to `x1FunctionFieldC k M`, compatible with $q$-expansions in the following sense: for every $b$ in `chartAlgFin` there is a Laurent series $y_b$ with coefficients in $Pl$ whose coefficientwise image under $Pl \hookrightarrow \overline{\mathbb Q}$ is `coeffEmb (AlgebraicClosure ℚ)` applied to the $q$-expansion of $b$, and such that the $q$-expansion of $\pi_{\mathrm{Fin}}(b)$ is the coefficientwise image of $y_b$ under $\pi_k$; likewise for every $b$ in `chartAlgInf` and $\pi_{\mathrm{Inf}}$.
--
--   (7) Two chart-centre laws for $\mathrm{Mdl}$. For every section $y$ of $\mathrm{Mdl}$`.toBase` over $\operatorname{Spec} k$ and every ring homomorphism $\beta$ from `chartAlgFin ℤ_{(p)} F₁ j` to $k$: if $y$ followed by $e$ followed by the first projection equals $\operatorname{Spec}$ of $\beta$ followed by `ιFin`, then for every $b$ in `chartAlgFin` the element $\pi_{\mathrm{Fin}}(b) - \beta(b)$ of `x1FunctionFieldC k M` lies in the non-units of the valuation subring of $\mathrm{Mdl}$`.pointEquivPlace y`. The same holds with `chartAlgInf`, `ιInf` and $\pi_{\mathrm{Inf}}$.
--
--   (8) A map $r$ from the places of $\mathcal F$ over $\overline{\mathbb Q}$ to the places of `x1FunctionFieldC k M` over $k$ subject to two conditions, which together form the conclusion of the theorem.
--
--   First, [`ModularCurve.IsLaurentPlaceReduction Pl πk F₁ (x1FunctionFieldC k M) r`](def/ModularCurve_QExpReductionModL.html#L18) holds: the degree of $r(P)$ equals the degree of $P$ for every place $P$; and for every Laurent series $y$ with coefficients in $Pl$ such that its coefficientwise image under $Pl \hookrightarrow \overline{\mathbb Q}$ lies in $\mathcal F$ and its coefficientwise image under $\pi_k$ lies in `x1FunctionFieldC k M` and is nonzero, and for every divisor $D$ on $\mathcal F$ whose value at each place $P$ is the order of the first of these images at $P$, the pushforward `Finsupp.mapDomain r D` has, at every place $Q$ of `x1FunctionFieldC k M`, value the order at $Q$ of the second image; that is, $r$ carries the divisor of a $Pl$-integral Laurent series to the divisor of its reduction.
--
--   Second, $r$ computes reduction of points: for every $Pl$-valued point $x_A$ of the two-chart model over $\operatorname{Spec} \rho_0$ (a morphism $\operatorname{Spec} Pl \to$ `TwoChartIntegralModel ℤ_{(p)} F₁ j` whose composite with `toBase` is $\operatorname{Spec}$ of $\rho_0$), every section $x$ of $M_\eta$`.toBase` and every section $y$ of $\mathrm{Mdl}$`.toBase`, if the composite of $x$ with $e_\eta$ and the first projection equals $\operatorname{Spec}$ of the inclusion $Pl \hookrightarrow \overline{\mathbb Q}$ followed by $x_A$, and the composite of $y$ with $e$ and the first projection equals $\operatorname{Spec}$ of $\pi_k$ followed by $x_A$, then $\mathrm{Mdl}$`.pointEquivPlace y` is the image under $r$ of $M_\eta$`.pointEquivPlace x`.
--
--   This packages Igusa's two-chart integral model of the function field of $X_1(M)$ over $\mathbb Z_{(p)}$ for $p \nmid M$ into a single statement: its generic fibre as a smooth proper curve over $\overline{\mathbb Q}$ with Galois-equivariant places pinned by the centres of the chart functions, its fibre over an arbitrary residue map $\pi_k : Pl \to k$, the coefficientwise reduction of the chart algebras, and a Deuring-type reduction map on places compatible with specialisation of points. It is the geometric input used in the comparison of divisor classes of points on $X_1$ with their reductions modulo $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom.lean

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem ModularCurve.exists_curveModels_twoChartIntegralModel_x1FunctionField_chartCentre_isLaurentPlaceReduction_of_ringHom
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (j : ↥(ModularCurve.x1FunctionField M)) [Fact (j ≠ 0)] (hj : ((j : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) = ModularCurve.jqModC ℚ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (πk : ↥Pl →+* k) :
    ∃ (Mη : CurveModel (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)))
      (eη : Mη.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eη)
      (_ : eη ≫ pullback.snd _ _ = Mη.toBase)

      (_ : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* (AlgebraicClosure ℚ)),
        x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
          (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
            algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) (β b) ∈ (Mη.pointEquivPlace x).toValuationSubring.nonunits)
      (_ : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* (AlgebraicClosure ℚ)),
        x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j),
          (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ),
              ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(ModularCurve.x1FunctionField M)).2⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M))) -
            algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) (β b) ∈ (Mη.pointEquivPlace x).toValuationSubring.nonunits)

      (_ : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (σ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ eη ≫ pullback.fst _ _ →
        Mη.pointEquivPlace x' = ModularCurve.arithmeticGalois (L := (AlgebraicClosure ℚ)) (ModularCurve.x1FunctionField M) σ • Mη.pointEquivPlace x)

      (ρ₀ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥Pl) (_ : Pl.subtype.comp ρ₀ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))

      (Mdl : CurveModel k ↥(ModularCurve.x1FunctionFieldC k M))
      (e : Mdl.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) (Spec.map (CommRingCat.ofHom (πk.comp ρ₀))))
      (_ : IsIso e) (_ : e ≫ pullback.snd _ _ = Mdl.toBase)

      (πFin : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M)) (πInf : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* ↥(ModularCurve.x1FunctionFieldC k M))
      (_ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), ∃ yb : LaurentSeries ↥Pl,
        ModularCurve.coeffMap Pl.subtype yb = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ∧
          ((πFin b : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk yb)
      (_ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), ∃ yb : LaurentSeries ↥Pl,
        ModularCurve.coeffMap Pl.subtype yb = ModularCurve.coeffEmb (AlgebraicClosure ℚ) ((b : ↥(ModularCurve.x1FunctionField M)) : LaurentSeries ℚ) ∧
          ((πInf b : ↥(ModularCurve.x1FunctionFieldC k M)) : LaurentSeries k) = ModularCurve.coeffMap πk yb)

      (_ : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* k),
        y.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πFin b - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (β b) ∈ (Mdl.pointEquivPlace y).toValuationSubring.nonunits)
      (_ : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}) (β : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j) →+* k),
        y.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom β) ≫ AlgebraicCurve.TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j), πInf b - algebraMap k ↥(ModularCurve.x1FunctionFieldC k M) (β b) ∈ (Mdl.pointEquivPlace y).toValuationSubring.nonunits)

      (r : Place (AlgebraicClosure ℚ) ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.x1FunctionField M)) → Place k ↥(ModularCurve.x1FunctionFieldC k M)),
      ModularCurve.IsLaurentPlaceReduction Pl πk (ModularCurve.x1FunctionField M) (ModularCurve.x1FunctionFieldC k M) r ∧

      ∀ (xA : NeronModelInfra.SchemeHomOver (Spec.map (CommRingCat.ofHom ρ₀)) (AlgebraicCurve.TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(ModularCurve.x1FunctionField M) j))
        (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : {q : Spec (CommRingCat.of k) ⟶ Mdl.C // q ≫ Mdl.toBase = 𝟙 _}),
        x.1 ≫ eη ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom Pl.subtype) ≫ xA.1 →
        y.1 ≫ e ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom πk) ≫ xA.1 →
        Mdl.pointEquivPlace y = r (Mη.pointEquivPlace x) := by sorry
