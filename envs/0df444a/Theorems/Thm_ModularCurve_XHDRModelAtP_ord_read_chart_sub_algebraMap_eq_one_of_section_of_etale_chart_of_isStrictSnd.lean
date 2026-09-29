-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd
-- name    : ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/2cd6e2b0-8654-5d40-89a4-29942f60f7a8
-- title:
--   Étale chart coordinate minus its value is a uniformiser
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (`hHp`: every $u$ with `ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1` lies in $H$), and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be a model package `XHDRModelAtP p M H hpM hj`: this bundles the integral model `X p (ΓM M H) hj` over `R p` with properness, flatness, integrality, local finite presentation and normality of its charts, properness and relative-dimension-one smoothness at level `ΓN p M H hpM`, a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $F_M :=$ `xHFunctionFieldBar M H` (the $\overline{\mathbb{Q}}$-base change of the function field of $X_H(M)$ inside $\overline{\mathbb{Q}}((q))$), an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of $\mathfrak{X}.\mathrm{Meta}.C$ with the geometric generic fibre, Galois equivariance of the induced dictionary between $\overline{\mathbb{Q}}$-points and places, the pinning of chart functions to $q$-expansions, and the further data of the structure (fibre curve model `Mfib`, the comparison morphism `efib`, the two component maps `comp i` for $i \in \mathrm{Fin}\,2$, and the isomorphism `w`).
--
--   Arithmetic data. $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with `hA : A.LiesOverPrime p`, i.e. $p$ lies in the nonunits of $A$; its residue field $\kappa$ has characteristic $p$ and is algebraically closed; $\rho : R_p \to A$ is a ring homomorphism with `hρ` asserting that $\rho$ followed by the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$.
--
--   Diamond data. $pb$ is a unit of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\overline{F} :=$ `JHNeronObjectAtP.Fbar p M H hpM κ` $=$ `qExpFunctionFieldC κ (ΓN p M H hpM)` over $\kappa$ which, by `hδ`, is the action through `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M/p) pb)`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Further, $SS$ is a finset of pairs of places of $\overline{F}$ whose members are exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p` (`hSS`), that is, the pairs $s$ with $s.2$ a supersingular place and $s.1$ the pullback of $s.2$ along the mod-$p$ Frobenius.
--
--   Correspondence and specialisation data. $\theta$ is a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, $\alpha : F_{M/p} \to F_M$ a $\overline{\mathbb{Q}}$-algebra map from `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)`, with `hα` that $\alpha$ is integral and `hβ` that $\theta \circ \alpha$ is integral. `Psp : JHPlaceSpecialization p M H hpM A` provides a specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\overline{F}$ together with a map on degree-zero divisor classes and its compatibilities: the $q$-expansion/divisor laws `d0_qexp`, `d5` and `spPic0_compat`, surjectivity `d4`, and the inertia and Frobenius equivariance `d6_inertia`, `d6_frobenius`. `Rpd : Psp.ProlongationDatum θ` provides two regular prolongations $R_1, R_2$ of $F_M$ to $\overline{F}$ over $A$ with the residue identification along $q$-expansions and the relation $f \in R_2 \iff \theta f \in R_1$, the residue of $f$ for $R_2$ being that of $\theta f$ for $R_1$.
--
--   Compatibility hypotheses. `hwgen`: for two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, if $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, `pullback.fst` and $\mathfrak{X}.w.\mathrm{hom}$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and `pullback.fst`, then the associated places satisfy $\mathrm{pointEquivPlace}\,y' = \mathrm{ofAlgAut}(\theta) \cdot \mathrm{pointEquivPlace}\,y$. `hα_coe`: $\alpha$ is the identity on underlying Laurent series. `hTD`: the dichotomy that for every place $W$ of $F_M$ either $\mathrm{sp}(W|_\alpha)$ equals the Frobenius pullback of $\delta(\mathrm{sp}(W|_{\theta\alpha}))$, or $\delta$ applied to the Frobenius pullback of $\mathrm{sp}(W|_\alpha)$ equals $\delta(\mathrm{sp}(W|_{\theta\alpha}))$. `hmodel`: `Rpd.IsModel`, the conjunction of the two divisor laws `DivisorLawFst`, `DivisorLawSnd` and the two cusp laws `CuspLawInfty`, `CuspLawZero` for $\alpha$, $\theta\alpha$ and $\delta$. `hcompat` and `hcompat'`: for each $i \in \mathrm{Fin}\,2$, each $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, each $A$-section $u$ of `toBase p (ΓM M H) hj` over `Spec.map ρ` whose generic point is $y$, each $\kappa$-section $u_\kappa$ of the fibre `fibre ((residue A).comp ρ)` reducing $u$, and each closed point $P_0$ of $(\mathfrak{X}.\mathrm{Mfib}\ A\ hA\ \rho\ h\rho).C$ sent by `efib` followed by `comp i` to the special point of $u_\kappa$: `hcompat` asserts that the place `placeOfPoint P0` equals `Psp.reduceFst α hα (pointEquivPlace y)` $= \mathrm{sp}(\mathrm{pointEquivPlace}\,y|_\alpha)$ when $i = 0$ and `Psp.reduceSnd (θ ∘ α) hβ δ (pointEquivPlace y)` $= \delta(\mathrm{sp}(\mathrm{pointEquivPlace}\,y|_{\theta\alpha}))$ otherwise; `hcompat'` asserts, in the same situation, that for $i = 0$ the place `Psp.reduceSnd (θ ∘ α) hβ δ (pointEquivPlace y)` equals $\delta$ applied to the Frobenius pullback `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p` of `placeOfPoint P0`, and for $i \neq 0$ that `Psp.reduceFst α hα (pointEquivPlace y)` equals the Frobenius pullback of `placeOfPoint P0`.
--
--   The strict place of the second kind. $Q$ is a place of $F_M$ over $\overline{\mathbb{Q}}$ with `hQ : Psp.IsStrictSnd α (θ ∘ α) hα hβ δ Q`, i.e. `Psp.reduceFst α hα Q` equals the Frobenius pullback of `Psp.reduceSnd (θ ∘ α) hβ δ Q`, and the latter place does not satisfy the predicate `Fixed` for $\delta$. Accompanying it: an $A$-section $u$ of the model, a $\kappa$-point $u_\kappa$ of the fibre, and a closed point $P_0$ of the fibre curve model, subject to `hu` (the generic point of $u$, i.e. `barPt A` followed by $u$, is the $\overline{\mathbb{Q}}$-point `pointEquivPlace.symm Q` followed by $\mathfrak{X}.\mathrm{eeta}$ and `pullback.fst`), `huκ₁` and `huκ₂` (that $u_\kappa$ followed by `pullback.fst` is the reduction of $u$ and that $u_\kappa$ followed by `pullback.snd` is the identity), `hP0` (that $P_0$ lies over the special point of $u_\kappa$ via `efib` followed by `comp 1`), `hP0Q` (that `placeOfPoint P0` $=$ `Psp.reduceSnd (θ ∘ α) hβ δ Q`), and `hsmooth` (that the special point of $u_\kappa$ is not in the image of `comp 0`).
--
--   The étale chart. $U$ is an open of `XO (ΓM M H) hj ρ`, the base change of the model along $\rho$, containing the image $x_0$ of the special point of $u_\kappa$ under `bcMap (ΓM M H) hj ρ (residue A) rfl` (`hxU`); $f : U \to \operatorname{Spec} A[X]$ is a morphism which is a morphism over $\operatorname{Spec} A$ (`hover`: $f$ followed by $\operatorname{Spec}$ of $A \to A[X]$ equals $U.\iota$ followed by the structure map `pullback.snd`), which is étale (`het`), and which sends the given point of $U$ to the image of the closed point of $\operatorname{Spec} A$ under $\operatorname{Spec}$ of evaluation at $0$ (`hpt`), i.e. to the origin of the special fibre of the affine line over $A$.
--
--   Conclusion. Write $X_Q$ for the geometric generic fibre `pullback (toBase p (ΓM M H) hj) (Spec.map (algebraMap (R p) (AlgebraicClosure ℚ)))`, $\mathrm{prA} : X_Q \to$ `XO (ΓM M H) hj ρ` for the map induced by the identity and $\operatorname{Spec}$ of $A \hookrightarrow \overline{\mathbb{Q}}$, $x_0$ as above, and $g_T \in \Gamma(\mathrm{XO}, U.\iota({\top}))$ for the section corresponding under $(U.\iota.\mathrm{appIso}\ \top)^{-1}$ to the pullback $f^{\ast}X$ of the coordinate. Then, assuming `hgen` that the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ lies in $\mathfrak{X}.\mathrm{eeta}^{-1}(\mathrm{prA}^{-1}(U.\iota(\top)))$, and letting $\mathrm{read} : \Gamma(\mathrm{XO}, U.\iota(\top)) \to F_M$ be the ring homomorphism given by restriction along $\mathrm{prA}$, then along $\mathfrak{X}.\mathrm{eeta}$, then the germ at the generic point, then $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}^{-1}$, and $\mathrm{param} := \mathrm{read}\,g_T$, the following holds: for every place $W$ of $F_M$ over $\overline{\mathbb{Q}}$ which is rational (the structure map $\overline{\mathbb{Q}} \to W.\mathrm{ResidueField}$ is surjective), every morphism $s : \operatorname{Spec} A \to U$ such that $s$ followed by $U.\iota$ and the structure map is the identity, such that `barPt A` followed by $s$ and $U.\iota$ equals the $\overline{\mathbb{Q}}$-point `pointEquivPlace.symm W` followed by $\mathfrak{X}.\mathrm{eeta}$ and $\mathrm{prA}$, and such that $U.\iota$ of the special point $s(\mathfrak{m}_A)$ is $x_0$, and every ring homomorphism $\chi : A[X] \to A$ with $s$ followed by $f$ equal to $\operatorname{Spec}\chi$:
--
--   (i) $\chi(X) \in \mathfrak{m}_A$; (ii) $\mathrm{param} \in W.\mathrm{toValuationSubring}$; (iii) $W.\mathrm{evalAt}(\mathrm{param})$ equals the image of $\chi(X)$ in $\overline{\mathbb{Q}}$; and (iv) $W.\mathrm{ord}\bigl(\mathrm{param} - \mathrm{algebraMap}\,\overline{\mathbb{Q}}\,F_M(\chi(X))\bigr) = 1$, where `Place.ord` is minus the logarithm of the adic valuation, so that the value $1$ says that $\mathrm{param}$ minus its value at $W$ is a uniformiser at $W$.
--
--   On the residue disc of a smooth point of the special fibre, an étale coordinate on a chart of the model, read in the geometric function field and normalised by subtracting its value along an $A$-section, is a uniformiser at the rational place cut out by that section, and the coordinate value lies in the maximal ideal of $A$. The result feeds [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd), where the disc parameter so obtained is used to identify the stalk of the reading homomorphism with a power series ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd.lean

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

theorem ModularCurve.XHDRModelAtP.ord_read_chart_sub_algebraMap_eq_one_of_section_of_etale_chart_of_isStrictSnd
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

    (Q : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQ : Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hu : barPt A ≫ u.1 = ((𝔛.Meta).pointEquivPlace.symm Q).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (hP0 : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP0Q : (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q)
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base)

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
