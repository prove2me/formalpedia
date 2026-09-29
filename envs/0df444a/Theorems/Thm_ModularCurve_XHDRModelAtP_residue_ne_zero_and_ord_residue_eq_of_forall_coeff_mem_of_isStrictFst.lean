-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst
-- name    : ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/2bfad943-0604-5a2c-8740-9fb0665ea1ff
-- title:
--   First unit coefficient computes the residue order at a strict place
-- statement:
--   Fix a prime $p$ and a natural number $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`), and the hypothesis `hj` that the $q$-series `jqModC ℚ` lies in the $q$-expansion function field $\mathbb{Q}$-subfield attached to the full group $SL_2(\mathbb{Z})$. Let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport style integral model datum for $X_H(M)$ over $R_p$, carrying in particular the geometric curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $F :=$ `xHFunctionFieldBar M H`, the isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the base change of the model to $\overline{\mathbb{Q}}$, and the involution-type morphism $\mathfrak{X}.w$.
--
--   Arithmetic data. $A$ is a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ (`hA`), whose residue field $\kappa :=$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed, together with a ring homomorphism $\rho : R_p \to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map $R_p \to \overline{\mathbb{Q}}$ (`hρ`). Write $\bar F :=$ `JHNeronObjectAtP.Fbar p M H hpM κ` for the $q$-expansion function field over $\kappa$ at level $\Gamma_N(p,M,H)$, and $F' :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the level-$M/p$ geometric function field for the image subgroup of $H$.
--
--   Diamond datum. $pb$ is a unit of $\mathbb{Z}/(M/p)$ whose underlying residue is $p$ (`hpb`), and $\delta$ is a self-map of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, is the action on places of the semilinear automorphism attached to the diamond automorphism `diamondActionModL` of $\bar F$ evaluated at [`CuspForm.gammaLift (M / p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36).
--
--   Node data. $SS$ is a finite set of pairs of places of $\bar F$ over $\kappa$ which, by `hSS`, consists exactly of the pairs in `ssNodePairsQExp κ (ΓN p M H hpM) p`, i.e. of the pairs $(s_1,s_2)$ with $s_2$ a supersingular place and $s_1$ the mod-$p$ Frobenius place of $s_2$.
--
--   Correspondence and specialisation data. $\theta$ is an $\overline{\mathbb{Q}}$-algebra automorphism of $F$; $\alpha : F' \to F$ is an $\overline{\mathbb{Q}}$-algebra homomorphism, with `hα` asserting that $\alpha$ is integral and `hβ` that $\theta \circ \alpha$ is integral; $Psp$ is a `JHPlaceSpecialization p M H hpM A`, i.e. a specialisation map $\mathrm{sp}$ from places of $F'$ over $\overline{\mathbb{Q}}$ to places of $\bar F$ over $\kappa$ together with a map on degree-zero divisor classes and the compatibility clauses of that structure (order formulae for $q$-expansions, surjectivity, inertia and Frobenius equivariance, compatibility on $\mathrm{Pic}^0$); and $Rpd$ is a `ProlongationDatum` for $Psp$ and $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F$ with residue maps onto $\bar F$ (each given by a valuation subring `integers` of $F$ and a surjective ring homomorphism `residue` onto $\bar F$ with kernel the maximal ideal, compatible with $A$), subject to the stated compatibility of $R_1$ with coefficientwise reduction of Laurent series and of $R_2$ with $R_1$ through $\theta$. As usual $\mathrm{red}_1(W) := Psp.\mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2(W) := \delta(Psp.\mathrm{sp}(W|_{\theta \circ \alpha}))$ denote the two reductions of a place $W$ of $F$, the restrictions being taken along the integral maps $\alpha$, resp. $\theta \circ \alpha$.
--
--   Compatibility hypotheses. `hwgen`: for any two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, if $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the first projection and $\mathfrak{X}.w$ agrees with $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection, then the place attached to $y'$ is the image of the place attached to $y$ under the semilinear automorphism of $\theta$. `hα_coe`: $\alpha$ is the identity on underlying Laurent series. `hTD`: the dichotomy `Psp.TypeDichotomy`, namely that for every place $W$ of $F$ either $\mathrm{red}_1(W)$ is the mod-$p$ Frobenius place of $\mathrm{red}_2(W)$, or $\delta$ applied to the Frobenius place of $\mathrm{red}_1(W)$ equals $\mathrm{red}_2(W)$. `hmodel`: $Rpd$ `IsModel` for $\alpha$, $\theta\circ\alpha$, $\delta$, the conjunction of the four clauses `DivisorLawFst`, `DivisorLawSnd`, `CuspLawInfty` and `CuspLawZero`. `hcompat`: for each $i \in \{0,1\}$, each $\overline{\mathbb{Q}}$-section $y$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$, each $A$-section $u$ of `toBase p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$ whose $\overline{\mathbb{Q}}$-point is the point attached to $y$, each $\kappa$-point $u_\kappa$ of the fibre at $\mathrm{residue} \circ \rho$ reducing $u$ and splitting the second projection, and each closed point $P_0$ of the special-fibre curve $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$ lying over the closed point of $u_\kappa$ through $\mathfrak{X}.\mathrm{efib}$ followed by the $i$-th component map $\mathfrak{X}.\mathrm{comp}\,i$: the place of $P_0$ equals $\mathrm{red}_1$ of the place of $y$ if $i = 0$, and $\mathrm{red}_2$ of that place if $i = 1$. `hcompat'`: under the same data, if $i = 0$ then $\mathrm{red}_2$ of the place of $y$ equals $\delta$ of the mod-$p$ Frobenius place of the place of $P_0$, and if $i = 1$ then $\mathrm{red}_1$ of the place of $y$ equals the mod-$p$ Frobenius place of the place of $P_0$.
--
--   The strict place and its section. $Q$ is a place of $F$ over $\overline{\mathbb{Q}}$ with `hQ` : `Psp.IsStrictFst`, that is, $\delta$ applied to the mod-$p$ Frobenius place of $\mathrm{red}_1(Q)$ equals $\mathrm{red}_2(Q)$, and $\mathrm{red}_1(Q)$ does not satisfy the predicate `Fixed` for $\delta$. Furthermore $u$ is an $A$-section of `toBase p (ΓM M H) hj` over $\mathrm{Spec}\,\rho$, $u_\kappa$ a morphism from $\mathrm{Spec}\,\kappa$ to the fibre at $\mathrm{residue}\circ\rho$, and $P_0$ a closed point of $(\mathfrak{X}.\mathrm{Mfib}\,A\,hA\,\rho\,h\rho).C$, subject to: `hu`, the $\overline{\mathbb{Q}}$-point of $u$ is the point corresponding to $Q$ under $\mathfrak{X}.\mathrm{Meta}.\mathrm{pointEquivPlace}$ composed with $\mathfrak{X}.\mathrm{eeta}$ and the first projection; `huκ₁`, the first projection of $u_\kappa$ is the reduction of $u$ along $A \to \kappa$; `huκ₂`, the second projection of $u_\kappa$ is the identity; `hP0`, the image of $P_0$ under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\,0$ is the closed point of $u_\kappa$; `hP0Q`, the place of $P_0$ is $\mathrm{red}_1(Q)$; and `hsmooth`, the closed point of $u_\kappa$ does not lie in the image of the other component map $\mathfrak{X}.\mathrm{comp}\,1$.
--
--   Abbreviations used in the conclusion. $X_{\overline{\mathbb{Q}}}$ is the base change of `toBase p (ΓM M H) hj` to $\overline{\mathbb{Q}}$; $\mathrm{prA} : X_{\overline{\mathbb{Q}}} \to X_{\mathcal{O}} :=$ `XO (ΓM M H) hj ρ` is the map of pullbacks induced by $A \hookrightarrow \overline{\mathbb{Q}}$; $\mathrm{bcA}$ is the base-change morphism from the fibre at $\mathrm{residue}\circ\rho$ to $X_{\mathcal{O}}$; and $x_0 \in X_{\mathcal{O}}$ is the image under $\mathrm{bcA}$ of the closed point of $u_\kappa$.
--
--   Conclusion. Let $hsp$ witness that the image under $\mathrm{prA}$ of the image under $\mathfrak{X}.\mathrm{eeta}$ of the generic point of $\mathfrak{X}.\mathrm{Meta}.C$ specialises to $x_0$, and let $\mathrm{emb} : \mathcal{O}_{X_{\mathcal{O}},x_0} \to F$ be the germ-reading homomorphism obtained as the specialisation map for $hsp$, followed by the stalk map of $\mathrm{prA}$, the stalk map of $\mathfrak{X}.\mathrm{eeta}$ at the generic point, and the inverse of $\mathfrak{X}.\mathrm{Meta}.\mathrm{ffEquiv}$. Let $u_t : \mathrm{Spec}\,A \to X_{\mathcal{O}}$ be the section determined by $u$, assume $hx$ that $u_t$ sends the closed point of $A$ to $x_0$, and let $\chi : \mathcal{O}_{X_{\mathcal{O}},x_0} \to A$ be the corresponding evaluation of germs (the specialisation map followed by $\mathrm{stalkClosedPointTo}\,u_t$). Then for every ring homomorphism $\Theta : \mathcal{O}_{X_{\mathcal{O}},x_0} \to A[[X]]$ satisfying
--
--   (i) $\Theta$ sends the germ of a base element $a \in A$ to the constant series $C(a)$;
--
--   (ii) for all $n$ and all germs $b$: all coefficients of $\Theta b$ in degrees $< n$ vanish if and only if $b \in (\ker \chi)^n$;
--
--   (iii) for all $n$ and every $q \in A[[X]]$ there is a germ $b$ with $\mathrm{coeff}_k(\Theta b) = \mathrm{coeff}_k(q)$ for all $k < n$;
--
--   and for every germ $b \in \mathcal{O}_{X_{\mathcal{O}},x_0}$ with $hb : \mathrm{emb}\,b \in R_1.\mathrm{integers}$, both of the following hold.
--
--   First, for every $k \in \mathbb{N}$: if $\mathrm{coeff}_i(\Theta b)$ lies in the maximal ideal of $A$ for all $i < k$ while $\mathrm{coeff}_k(\Theta b)$ does not, then $R_1.\mathrm{residue}\langle \mathrm{emb}\,b, hb\rangle \neq 0$ and the order of that residue at the place $\mathrm{red}_1(Q) = Psp.\mathrm{reduceFst}\,\alpha\,h\alpha\,Q$ of $\bar F$ equals $k$.
--
--   Second, conversely, if $R_1.\mathrm{residue}\langle \mathrm{emb}\,b, hb\rangle \neq 0$ then there exists $k$ with $\mathrm{coeff}_k(\Theta b) \notin \mathfrak{m}_A$.
--
--   This is the reduction law for expansions along the residue disc of a strict place of the first kind on the Deligne–Rapoport model of $X_H(M)$ at $p \parallel M$: reducing the $A$-coefficients of the expansion of a germ along the section $u$ yields the expansion of its $R_1$-residue at the corresponding point of the component indexed by $0$, so the first coefficient that is a unit records the order of vanishing of the residue at $\mathrm{red}_1(Q)$. It is used by [`ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst`](thm.html#ModularCurve.XHDRModelAtP.exists_discParameter_ringHom_powerSeries_range_stalk_read_of_isStrictFst), which produces a disc parameter and the corresponding power-series expansion of germs at such a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst.lean

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

theorem ModularCurve.XHDRModelAtP.residue_ne_zero_and_ord_residue_eq_of_forall_coeff_mem_of_isStrictFst
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
    (hsmooth : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ 1).base) :
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

    ∀ (b : ↥((XO (ΓM M H) hj ρ).presheaf.stalk x₀)) (hb : emb b ∈ Rpd.R₁.integers),
      (∀ k : ℕ, (∀ i < k, PowerSeries.coeff i (Θ b) ∈ maximalIdeal ↥A) → PowerSeries.coeff k (Θ b) ∉ maximalIdeal ↥A →
        Rpd.R₁.residue ⟨emb b, hb⟩ ≠ 0 ∧
          (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨emb b, hb⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = k) ∧
      (Rpd.R₁.residue ⟨emb b, hb⟩ ≠ 0 → ∃ k : ℕ, PowerSeries.coeff k (Θ b) ∉ maximalIdeal ↥A) := by sorry
