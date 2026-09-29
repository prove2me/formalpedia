-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd
-- name    : ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1c98227b-5151-54d9-ae0a-279c05cd163a
-- title:
--   First unit coefficient computes the order of the reduced germ
-- statement:
--   Fix a prime $p$ and a natural number $M \neq 0$ with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), a subgroup $H \le (\mathbb{Z}/M)^\times$ which contains every unit whose image under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$ (`hHp`), with $M/p \neq 0$, and assume `hj`: the Laurent series `jqModC ℚ` of $j$ lies in the $q$-expansion function field $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ \mathrm{SL}_2(\mathbb{Z})$. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport-style model package for $X_H(M)$ over $R_p$: a proper, flat, integral, locally of finite presentation model `X p (ΓM M H) hj` with integrally closed affine sections, together with a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`, an isomorphism $\mathfrak{X}.\mathtt{eeta}$ of $\mathfrak{X}.\mathrm{Meta}.C$ with the base change of the model to $\overline{\mathbb{Q}}$, Galois equivariance of the induced bijection between $\overline{\mathbb{Q}}$-points and places, the pinning of the finite chart, smoothness and geometric integrality of the generic fibre, and the further data of the package (the components `𝔛.comp`, the morphism `𝔛.efib`, the curve model `𝔛.Mfib` of the special-fibre datum, the isomorphism `𝔛.w`, and the section `𝔛.ξinf`).
--
--   Arithmetic data at $p$: $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`, the predicate `LiesOverPrime`), whose residue field $\kappa = \mathrm{ResidueField}\ A$ has characteristic $p$ and is algebraically closed, and $\rho : R_p \to A$ is a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$ (`hρ`).
--
--   Diamond datum: $pb$ is a unit of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\mathrm{Fbar} = \mathrm{qExpFunctionFieldC}\ \kappa\ (\Gamma_N(p,M,H))$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)`, where `infSubgroup p M H hpM` is the image of $H$ in $(\mathbb{Z}/(M/p))^\times$. Node datum: $SS$ is a finite set of pairs of places of $\mathrm{Fbar}$ whose members are exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p` (`hSS`), that is, the pairs $s$ with $s_2$ a supersingular place and $s_1$ the image of $s_2$ under the mod-$p$ Frobenius map on places.
--
--   Correspondence data: $\theta$ is an automorphism of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, and $\alpha$ is a $\overline{\mathbb{Q}}$-algebra homomorphism from `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to `xHFunctionFieldBar M H`, with $\alpha$ integral (`hα`) and $\beta := \theta \circ \alpha$ integral (`hβ`); `hα_coe` states that $\alpha$ does not change Laurent series, $(\alpha u) = u$ as elements of $\mathrm{LaurentSeries}\ \overline{\mathbb{Q}}$. Further, $\mathrm{Psp}$ is a `JHPlaceSpecialization p M H hpM A`: a specialisation map $\mathrm{sp}$ from places of `xHFunctionFieldBar (M / p) (infSubgroup …)` to places of $\mathrm{Fbar}$ over $\kappa$, together with a homomorphism on degree-zero divisor class groups and the laws relating $\mathrm{sp}$ to $q$-expansions, surjectivity of $\mathrm{sp}$, realisation of divisors of functions, invariance under inertia, compatibility of Frobenius elements with `qExpFrobeniusPlaceModL`, and compatibility of the $\mathrm{Pic}^0$-map; and $\mathrm{Rpd}$ is a `JHPlaceSpecialization.ProlongationDatum Psp θ`: two regular prolongations $R_1, R_2$ of $A$ to `xHFunctionFieldBar M H` with residues in $\mathrm{Fbar}$, such that $R_1$ computes residues coefficientwise on Laurent series, $f$ lies in the integers of $R_2$ exactly when $\theta f$ lies in those of $R_1$, and the $R_2$-residue of $f$ is the $R_1$-residue of $\theta f$. Throughout, $\mathrm{red}_1(W) := \mathrm{Psp}.\mathtt{reduceFst}\ \alpha\ h\alpha\ W = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2(W) := \mathrm{Psp}.\mathtt{reduceSnd}\ \beta\ h\beta\ \delta\ W = \delta(\mathrm{sp}(W|_\beta))$, restriction being along the corresponding integral algebra map.
--
--   Compatibility hypotheses. `hwgen`: for any two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ (sections of $\mathfrak{X}.\mathrm{Meta}.\mathtt{toBase}$), if $y'$ followed by $\mathfrak{X}.\mathtt{eeta}$, the first pullback projection and $\mathfrak{X}.w.\mathrm{hom}$ equals $y$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection, then the place of $y'$ is the place of $y$ translated by the semilinear automorphism $\mathtt{ofAlgAut}\ \theta$. `hTD` is the type dichotomy $\mathrm{Psp}.\mathtt{TypeDichotomy}$: for every place $W$ of `xHFunctionFieldBar M H`, either $\mathrm{red}_1(W)$ is the mod-$p$ Frobenius image of $\mathrm{red}_2(W)$, or $\delta$ applied to the Frobenius image of $\mathrm{red}_1(W)$ equals $\mathrm{red}_2(W)$. `hmodel` is $\mathrm{Rpd}.\mathtt{IsModel}\ \alpha\ \beta\ h\alpha\ h\beta\ \delta$, the conjunction of the two divisor laws `DivisorLawFst`, `DivisorLawSnd` and the two cusp laws `CuspLawInfty α hα`, `CuspLawZero β hβ δ`. `hcompat` and `hcompat'` are the two reduction laws along the components, each quantified over $i \in \mathrm{Fin}\,2$, a $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{X}.\mathrm{Meta}.C$, a section $u$ of the model over $\mathrm{Spec}\,\rho$, a $\kappa$-point $u_\kappa$ of the fibre over $(\mathrm{residue}_A) \circ \rho$ and a closed point $P_0$ of $(\mathfrak{X}.\mathtt{Mfib}\ A\ hA\ \rho\ h\rho).C$, subject to: $u$ restricted along $A \hookrightarrow \overline{\mathbb{Q}}$ agrees with $y$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection; $u_\kappa$ followed by the first projection is the reduction of $u$ modulo the maximal ideal; $u_\kappa$ followed by the second projection is the identity; and $P_0$ maps, under $\mathfrak{X}.\mathtt{efib}$ followed by $\mathfrak{X}.\mathtt{comp}\ i$, to the image of the closed point under $u_\kappa$. Under these, `hcompat` asserts that the place of $P_0$ in $\mathfrak{X}.\mathtt{Mfib}$ is $\mathrm{red}_1$ of the place of $y$ if $i = 0$ and $\mathrm{red}_2$ of the place of $y$ otherwise, while `hcompat'` asserts that for $i = 0$ one has $\mathrm{red}_2(\text{place of }y) = \delta(\mathrm{Frob}_p(\text{place of }P_0))$ and for $i = 1$ one has $\mathrm{red}_1(\text{place of }y) = \mathrm{Frob}_p(\text{place of }P_0)$, $\mathrm{Frob}_p$ denoting `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`.
--
--   The place under consideration: $Q$ is a place of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ which is strict of the second kind, $\mathrm{hQ} : \mathrm{Psp}.\mathtt{IsStrictSnd}\ \alpha\ \beta\ h\alpha\ h\beta\ \delta\ Q$, i.e. $\mathrm{red}_1(Q) = \mathrm{Frob}_p(\mathrm{red}_2(Q))$ and the place $\mathrm{red}_2(Q)$ does not satisfy the predicate `Fixed` for $\delta$. Given in addition: a section $u$ of the model over $\mathrm{Spec}\,\rho$, a $\kappa$-point $u_\kappa$ of the fibre over $(\mathrm{residue}_A)\circ\rho$, and a closed point $P_0$ of $(\mathfrak{X}.\mathtt{Mfib}\ A\ hA\ \rho\ h\rho).C$, with `hu`: $u$ restricted to $\overline{\mathbb{Q}}$ is the point corresponding to $Q$ under $\mathfrak{X}.\mathrm{Meta}.\mathtt{pointEquivPlace}$, followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection; `huκ₁`, `huκ₂`: $u_\kappa$ followed by the first projection is the reduction of $u$, and followed by the second projection is the identity; `hP0`: $P_0$ lies, via $\mathfrak{X}.\mathtt{efib}$ followed by the component $\mathfrak{X}.\mathtt{comp}\ 1$, over the image of the closed point under $u_\kappa$; `hP0Q`: the place of $P_0$ is $\mathrm{red}_2(Q)$; and `hsmooth`: the image of the closed point under $u_\kappa$ is not in the image of the base map of the other component $\mathfrak{X}.\mathtt{comp}\ 0$.
--
--   Local data at the special point. Write $XQ$ for the base change of the model along $R_p \to \overline{\mathbb{Q}}$, $\mathrm{prA} : XQ \to XO$ for the canonical map to the base change $XO$ along $\rho$ induced by $A \hookrightarrow \overline{\mathbb{Q}}$, and $\mathrm{bcA} = \mathtt{bcMap}$ for the map from the fibre over $\kappa$ to $XO$ induced by the residue map; set $x_0 := \mathrm{bcA}(u_\kappa(\text{closed point}))$. The assertion is made for every specialisation relation $\mathrm{hsp}$ of $\mathrm{prA}(\mathfrak{X}.\mathtt{eeta}(\text{generic point of } \mathfrak{X}.\mathrm{Meta}.C))$ to $x_0$; with such an $\mathrm{hsp}$, $\mathrm{emb}$ denotes the ring homomorphism from the stalk of $XO$ at $x_0$ to `xHFunctionFieldBar M H` obtained by composing the specialisation map of stalks, the stalk map of $\mathrm{prA}$, the stalk map of $\mathfrak{X}.\mathtt{eeta}$ at the generic point, and the inverse of $\mathfrak{X}.\mathrm{Meta}.\mathtt{ffEquiv}$. Further, $u_t : \mathrm{Spec}\,A \to XO$ is the section determined by $u$ and the identity; the assertion is made for every proof $\mathrm{hx}$ that $u_t$ sends the closed point of $A$ to $x_0$, and $\chi$ denotes the evaluation homomorphism from the stalk at $x_0$ to $A$ obtained from the corresponding specialisation map of stalks followed by $\mathtt{stalkClosedPointTo}\ u_t$.
--
--   Finally, for every ring homomorphism $\Theta$ from the stalk of $XO$ at $x_0$ to the power series ring $A[[X]]$ such that: $\Theta$ sends the germ at $x_0$ of a constant $a \in A$ (the element `baseGerm ρ x₀ a` coming from the base) to the constant power series $\mathrm{C}\,a$; for all $n$ and all germs $b$, the coefficients of $\Theta b$ in degrees $< n$ all vanish if and only if $b \in (\ker \chi)^n$; and for all $n$ and every power series $q$ there is a germ $b$ with $\mathrm{coeff}_k(\Theta b) = \mathrm{coeff}_k(q)$ for all $k < n$ — the following holds for every germ $b$ in the stalk at $x_0$ and every proof $\mathrm{hb}$ that $\mathrm{emb}\,b$ lies in the integers of $R_2$:
--
--   first, for every $k$, if $\mathrm{coeff}_i(\Theta b)$ lies in the maximal ideal of $A$ for all $i < k$ and $\mathrm{coeff}_k(\Theta b)$ does not lie in the maximal ideal of $A$, then the $R_2$-residue of $\mathrm{emb}\,b$ is non-zero and its order at the place $\mathrm{red}_2(Q) = \mathrm{Psp}.\mathtt{reduceSnd}\ \beta\ h\beta\ \delta\ Q$ (the order $\mathrm{ord}$ of a place, the negative of the logarithm of its adic valuation) equals $k$;
--
--   second, if the $R_2$-residue of $\mathrm{emb}\,b$ is non-zero, then some coefficient $\mathrm{coeff}_k(\Theta b)$ lies outside the maximal ideal of $A$.
--
--   This is the reduction law for the expansion of germs along a residue disc on the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$: reducing the coefficients of the power series expansion of a germ along the given $A$-section recovers the expansion of its Gauss residue at the corresponding point of the special fibre, so the first coefficient which is a unit of $A$ records the order of vanishing of the residue at the place $\mathrm{red}_2(Q)$, together with the converse that a non-zero residue forces some unit coefficient. It feeds the construction of a disc parameter in [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictSnd), part of the analysis of places of the second kind used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd.lean

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

theorem ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictSnd
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
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 0).base) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl

    letI x₀ : ↥(XO (ΓM M H) hj ρ) := bcA.base (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    ∀ (hsp : prA.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ x₀),
    letI emb : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
          ((prA.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
            ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes hsp).hom))

    letI ut : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρ := pullback.lift u.1 (𝟙 _) (by rw [u.2, Category.id_comp])
    ∀ (hx : ut.base (IsLocalRing.closedPoint ↥A) = x₀),
    letI χ : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* ↥A :=
      (Scheme.stalkClosedPointTo ut).hom.comp ((XO (ΓM M H) hj ρ).presheaf.stalkSpecializes (specializes_of_eq hx)).hom

    ∀ (Θ : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀) →+* PowerSeries ↥A),
      (∀ a : ↥A, Θ (baseGerm ρ x₀ a) = PowerSeries.C a) →
      (∀ (n : ℕ) (b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀)),
        (∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = 0) ↔ b ∈ RingHom.ker χ ^ n) →
      (∀ (n : ℕ) (q : PowerSeries ↥A), ∃ b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀),
        ∀ k : ℕ, k < n → PowerSeries.coeff k (Θ b) = PowerSeries.coeff k q) →

    ∀ (b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀)) (hb : emb b ∈ Rpd.R₂.integers),
      (∀ k : ℕ, (∀ i < k, PowerSeries.coeff i (Θ b) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Θ b) ∉ maximalIdeal ↥A →
        Rpd.R₂.residue ⟨emb b, hb⟩ ≠ 0 ∧
          (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨emb b, hb⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
      (Rpd.R₂.residue ⟨emb b, hb⟩ ≠ 0 → ∃ k : ℕ, PowerSeries.coeff k (Θ b) ∉ maximalIdeal ↥A) := by sorry
