-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictFst
-- name    : ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/88a75996-da24-5b5b-ad0c-c33249d6ab7c
-- title:
--   Étale coordinate is a uniformiser at a rational place
-- statement:
--   Throughout, places are taken in the project's sense: a place of a field extension $F/K$ is a valuation subring of $F$ containing the image of $K$, different from $F$, whose valuation ring is a principal ideal ring; $\mathrm{ord}$ denotes the associated normalised order function ($-\log$ of the adic valuation), and a place is `IsRational` when $K$ surjects onto its residue field.
--
--   *Arithmetic data.* Fixed are a prime $p$, a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and divisibility hypotheses `hpM` : $p \mid M$ and `hpM2` : $p^2 \nmid M$, together with `hHp`, which requires every unit $u \in (\mathbb{Z}/M)^\times$ whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial to lie in $H$, and with $M/p$ nonzero. Further, `hj` states that the Laurent series `jqModC ℚ` lies in the $q$-expansion function field `qExpFunctionFieldC ℚ ⊤` of the full modular group, and $\mathfrak{X}$ is a package `XHDRModelAtP p M H hpM hj`: an integral model of $X_H(M)$ over `R p` whose fields include the properness, flatness, integrality and normality data of `toBase p (ΓM M H) hj`, a curve model $\mathfrak{X}.\mathtt{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H` (written $F_M$ below), an isomorphism $\mathfrak{X}.\mathtt{eeta}$ from $\mathfrak{X}.\mathtt{Meta}.C$ onto the base change of the model to $\overline{\mathbb{Q}}$, and the further components of that structure used below ($\mathfrak{X}.w$, $\mathfrak{X}.\mathtt{Mfib}$, $\mathfrak{X}.\mathtt{efib}$, $\mathfrak{X}.\mathtt{comp}$).
--
--   *Valuation data.* $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA` : `A.LiesOverPrime p`, i.e. $p$ is a non-unit of $A$; its residue field $\kappa$ has characteristic $p$ and is algebraically closed. A ring homomorphism $\rho : \mathtt{R}\,p \to A$ is given together with `hρ`, stating that $\rho$ followed by the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $\mathtt{R}\,p \to \overline{\mathbb{Q}}$.
--
--   *Frame of the degeneration.* A unit $pb$ of $\mathbb{Z}/(M/p)$ with underlying element $p$ is fixed (`hpb`). The operator $\delta$ on places of $\mathtt{Fbar}\,p\,M\,H\,hpM\,\kappa = \mathtt{qExpFunctionFieldC}\,\kappa\,(\Gamma_N\,p\,M\,H\,hpM)$ is, by `hδ`, the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the $\Gamma_0(M/p)$-lift of $pb$, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. A finite set $SS$ of pairs of places is given, `hSS` identifying its members with the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is, the pairs $(v_1,v_2)$ with $v_2$ in `ssPlacesQExp` and $v_1$ the mod-$p$ Frobenius place `qExpFrobeniusPlaceModL` of $v_2$. Next, $\theta$ is a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$ and $\alpha$ a $\overline{\mathbb{Q}}$-algebra homomorphism from $F_{M/p} = \mathtt{xHFunctionFieldBar}\,(M/p)\,(\mathtt{infSubgroup}\,p\,M\,H\,hpM)$ to $F_M$, with `hα` asserting integrality of $\alpha$ and `hβ` integrality of $\alpha$ followed by $\theta$; `hα_coe` asserts that $\alpha$ does not change underlying Laurent series, i.e. $\alpha u$ and $u$ have the same image in $\mathtt{LaurentSeries}\,\overline{\mathbb{Q}}$. Finally, $\mathit{Psp}$ is a specialisation datum `JHPlaceSpecialization p M H hpM A` (a map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\mathtt{Fbar}$ together with its divisor and Galois compatibilities), $\mathit{Rpd}$ a `ProlongationDatum` for $\mathit{Psp}$ and $\theta$, and the following compatibility hypotheses are imposed: `hwgen`, stating that for two $\overline{\mathbb{Q}}$-sections $y,y'$ of $\mathfrak{X}.\mathtt{Meta}.\mathtt{toBase}$ with $y'$ followed by $\mathfrak{X}.\mathtt{eeta}$, the first projection and $\mathfrak{X}.w.\mathtt{hom}$ equal to $y$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection, the associated places satisfy $\mathtt{pointEquivPlace}\,y' = \mathtt{SemilinearAut.ofAlgAut}\,\theta \cdot \mathtt{pointEquivPlace}\,y$; `hTD`, the type dichotomy for $(\alpha, \theta \circ \alpha, \delta)$, i.e. for every place $W$ of $F_M$ either $\mathtt{reduceFst}\,\alpha\,W$ is the Frobenius place of $\mathtt{reduceSnd}\,(\theta\circ\alpha)\,\delta\,W$ or $\delta$ of the Frobenius place of $\mathtt{reduceFst}\,\alpha\,W$ equals $\mathtt{reduceSnd}\,(\theta\circ\alpha)\,\delta\,W$ (here $\mathtt{reduceFst}\,\alpha\,W = \mathrm{sp}(W|_\alpha)$ and $\mathtt{reduceSnd}\,\beta\,\delta\,W = \delta(\mathrm{sp}(W|_\beta))$ for the restrictions along $\alpha$, resp. $\theta\circ\alpha$); `hmodel`, asserting that $\mathit{Rpd}$ is a model for $(\alpha,\theta\circ\alpha,\delta)$, a conjunction of the two divisor laws and the two cusp laws of `IsModel`; and the two compatibility hypotheses `hcompat` and `hcompat'`, which for each index $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-section $y$, each $A$-point $u$ of the model over $\rho$, each $\kappa$-point $u_\kappa$ of the fibre compatible with $u$ and splitting the fibre projection, and each closed point $P_0$ of $(\mathfrak{X}.\mathtt{Mfib}\,A\,hA\,\rho\,h\rho).C$ mapping to the special point of $u_\kappa$ under $\mathfrak{X}.\mathtt{efib}$ followed by $\mathfrak{X}.\mathtt{comp}\,i$, identify the place of $P_0$ with $\mathtt{reduceFst}\,\alpha\,(\mathtt{pointEquivPlace}\,y)$ for $i = 0$ and with $\mathtt{reduceSnd}\,(\theta\circ\alpha)\,\delta\,(\mathtt{pointEquivPlace}\,y)$ for $i = 1$ (`hcompat`), respectively express the other reduction of $\mathtt{pointEquivPlace}\,y$ through the mod-$p$ Frobenius place of the place of $P_0$, twisted by $\delta$ when $i = 0$ (`hcompat'`).
--
--   *The strict place of the first kind and its section.* A place $Q$ of $F_M$ over $\overline{\mathbb{Q}}$ is given with `hQ` : `Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q`, i.e. $\delta$ applied to the Frobenius place of $\mathtt{reduceFst}\,\alpha\,Q$ equals $\mathtt{reduceSnd}\,(\theta\circ\alpha)\,\delta\,Q$ and $\mathtt{reduceFst}\,\alpha\,Q$ does not satisfy the predicate `Fixed` for $\delta$. Accompanying it are: an $A$-point $u$ of `toBase p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$, a $\kappa$-point $u_\kappa$ of the fibre of the model at the residue map composed with $\rho$, and a closed point $P_0$ of $(\mathfrak{X}.\mathtt{Mfib}\,A\,hA\,\rho\,h\rho).C$, subject to: `hu`, the generic point of $u$ is the point of $\mathfrak{X}.\mathtt{Meta}.C$ corresponding to $Q$ (i.e. $\mathtt{barPt}\,A$ followed by $u$ equals $\mathtt{pointEquivPlace}^{-1}Q$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection); `huκ₁` and `huκ₂`, saying that $u_\kappa$ followed by the first projection is the reduction of $u$ and that $u_\kappa$ splits the second projection; `hP0`, saying that $P_0$ maps under $\mathfrak{X}.\mathtt{efib}$ followed by $\mathfrak{X}.\mathtt{comp}\,0$ to the image of the closed point of $\kappa$ under $u_\kappa$; `hP0Q`, the place of $P_0$ equals $\mathtt{reduceFst}\,\alpha\,hα\,Q$; and `hsmooth`, that the special point of $u_\kappa$ is not in the image of $\mathfrak{X}.\mathtt{comp}\,1$.
--
--   *The étale chart.* Let $X_O = \mathtt{XO}\,(\Gamma_M\,M\,H)\,hj\,\rho$ be the base change of the model along $\rho$, $\mathtt{bcA} = \mathtt{bcMap}$ the reduction morphism from the fibre to $X_O$, and $x_0 = \mathtt{bcA}$ applied to the special point of $u_\kappa$. Given are an open subscheme $U$ of $X_O$ with `hxU` : $x_0 \in U$, a morphism $f : U \to \mathrm{Spec}\,A[X]$ with `hover` saying that $f$ followed by $\mathrm{Spec}$ of $A \to A[X]$ equals the inclusion of $U$ followed by the structure morphism to $\mathrm{Spec}\,A$ (so $f$ is a morphism over $A$), `het` : $f$ is étale, and `hpt` : $f$ sends $x_0$ to the image of the closed point of $A$ under $\mathrm{Spec}$ of evaluation at $0$, that is, to the origin of the special fibre of $\mathbb{A}^1_A$.
--
--   *Auxiliary constructions in the conclusion.* Write $X_{\overline{\mathbb{Q}}}$ for the base change of `toBase p (ΓM M H) hj` along $\mathtt{R}\,p \to \overline{\mathbb{Q}}$ and $\mathtt{prA} : X_{\overline{\mathbb{Q}}} \to X_O$ for the morphism induced by the identity on the model and $\mathrm{Spec}$ of the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$. Let $g_T$ be the global section of $X_O$ over the open image $\mathtt{U.ι}\,''ᵁ\,\top$ obtained by transporting, along the inverse of the section isomorphism of the open immersion, the pullback under $f$ of the coordinate $X \in A[X]$ viewed as a global section of $\mathrm{Spec}\,A[X]$. Assume (hypothesis `hgen`) that the generic point of $\mathfrak{X}.\mathtt{Meta}.C$ lies in the preimage of $\mathtt{U.ι}\,''ᵁ\,\top$ under $\mathtt{prA}$ followed by $\mathfrak{X}.\mathtt{eeta}$, and let $\mathrm{read}$ be the ring homomorphism from sections over $\mathtt{U.ι}\,''ᵁ\,\top$ to $F_M$ given by pulling back along $\mathtt{prA}$, then along $\mathfrak{X}.\mathtt{eeta}$, taking the germ at the generic point, and transporting along $\mathfrak{X}.\mathtt{Meta}.\mathtt{ffEquiv}^{-1}$. Put $\mathrm{param} = \mathrm{read}\,g_T \in F_M$, the chart coordinate read in the geometric function field.
--
--   *Conclusion.* For every place $W$ of $F_M$ over $\overline{\mathbb{Q}}$ that is rational, every morphism $s : \mathrm{Spec}\,A \to U$ such that $s$ followed by the inclusion of $U$ and the structure morphism to $\mathrm{Spec}\,A$ is the identity, such that $\mathtt{barPt}\,A$ followed by $s$ and the inclusion of $U$ equals the point of $\mathfrak{X}.\mathtt{Meta}.C$ attached to $W$ followed by $\mathfrak{X}.\mathtt{eeta}$ and $\mathtt{prA}$, and such that the image of the closed point of $A$ under $s$ and the inclusion of $U$ is $x_0$, and for every ring homomorphism $\chi : A[X] \to A$ with $s$ followed by $f$ equal to $\mathrm{Spec}\,\chi$, the following four assertions hold: $\chi(X)$ lies in the maximal ideal of $A$; $\mathrm{param}$ lies in the valuation subring of $W$; the value $W.\mathtt{evalAt}\,\mathrm{param}$ equals the image of $\chi(X)$ in $\overline{\mathbb{Q}}$; and $W.\mathrm{ord}\bigl(\mathrm{param} - \text{(image in } F_M \text{ of } \chi(X))\bigr) = 1$.
--
--   This is the smooth-point case of the local analysis of residue discs on the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: on the disc around a $\kappa$-rational point of one component lying off the other component, the coordinate of an étale chart over $A$, read in the geometric function field, takes a value in the maximal ideal of $A$ at a rational place of the disc and differs from that value by a uniformiser there. It is used by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst), which turns this uniformiser into a power-series parameter identifying the stalk of the chart reading.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictFst.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictFst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceFst α hα Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base)

    (U : (XO (ΓM M H) hj ρ).Opens) (hxU : (bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl).base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ U)
    (f : (U : Scheme.{0}) ⟶ Spec (CommRingCat.of (Polynomial ↥A)))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (Polynomial ↥A))) = U.ι ≫ pullback.snd _ _)
    (het : Etale f)
    (hpt : f.base ⟨_, hxU⟩ = (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : ↥A)))).base (IsLocalRing.closedPoint ↥A))
    :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))

    letI φT : Polynomial ↥A →+* Γ(Spec (CommRingCat.of (Polynomial ↥A)), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ↥A))).inv.hom
    letI gT : Γ(XO (ΓM M H) hj ρ, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φT Polynomial.X))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρ, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prA ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prA.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gT
    ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prA →
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = x₀ →
      ∀ (χ : Polynomial ↥A →+* ↥A), s ≫ f = Spec.map (CommRingCat.ofHom χ) →
        χ Polynomial.X ∈ maximalIdeal ↥A ∧
        param ∈ W.toValuationSubring ∧ W.evalAt param = ((χ Polynomial.X : ↥A) : AlgebraicClosure ℚ) ∧
        W.ord (param - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((χ Polynomial.X : ↥A) : AlgebraicClosure ℚ)) = 1 := by sorry
