-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
-- name    : ModularCurve.XHDRModelAtP.exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/883e7b6f-8619-510f-910d-cbbd2fabd58f
-- title:
--   Base change of a crossing chart along a second coefficient DVR
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, together with a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is $1$, and assume $j \in$ `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj` package for the model $X$ of level $\Gamma_M(M,H)$ over $R_p$. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, let $\rho : R_p \to A$ be compatible with $R_p \to \overline{\mathbb{Q}}$, and let $O$ be a discrete valuation domain with $\rho_O : R_p \to O$, $\mathfrak{m}_O = (p)$, and maps $t_\kappa : O \to \kappa(A)$, $j_O : O \to \overline{\mathbb{Q}}$, $\iota_A : O \to A$ fitting into the obvious compatibilities with $\rho$. Let $n$ be a point of the fibre product of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` into the fibre of $X$ over $\kappa(A)$, and let $x_n \in X_O := X \times_{\operatorname{Spec} R_p} \operatorname{Spec} O$ be the image of $n$ under the first projection followed by branch $0$ and by `bcMap`. Assume given $e \ge 1$, an open $U \ni x_n$ of $X_O$ and a morphism $f : U \to \operatorname{Spec}\bigl(O[X_0,X_1]/(X_0X_1 - p^e)\bigr)$ over $O$ such that: the locus where both coordinate classes `CrossingQuotient.U` and `CrossingQuotient.V` lie in the prime $f(y)$ is exactly the fibre of $U$ over $x_n$; at each $y$ over $x_n$ the stalk map of $f$ is flat, carries the maximal ideal onto the maximal ideal and induces an isomorphism of residue fields; each such $y$ has an open neighbourhood $V$ in $U$ with $V \hookrightarrow U \to$ the crossing scheme étale; and the vanishing of `CrossingQuotient.V` (resp. `CrossingQuotient.U`) at $y$ is equivalent to $y$ lying in the image of branch $0$ (resp. branch $1$). Finally let $O'$ be a discrete valuation domain, $\sigma : O \to O'$, and $\iota_{A'} : O' \to A$ an injective local homomorphism with $\iota_{A'} \circ \sigma = \iota_A$, together with $j_{O'} : O' \to \overline{\mathbb{Q}}$ and the compatibilities $j_{O'} \circ (\sigma \circ \rho_O) =$ the structural map, $A \hookrightarrow \overline{\mathbb{Q}}$ after $\iota_{A'}$ equal to $j_{O'}$, and $\mathrm{res}_A \circ \iota_{A'} \circ \sigma \circ \rho_O = \mathrm{res}_A \circ \rho$. Write $W$ for the image open $U.\iota{}''\top$, $g_u, g_v \in \Gamma(X_O, W)$ for the sections obtained from the two coordinate classes by $f$, $\mathrm{pr}_\sigma : X_{O'} \to X_O$ for the map induced by $\sigma$, $x_n'$ for the point of $X_{O'} := X \times_{\operatorname{Spec} R_p} \operatorname{Spec} O'$ built from $n$ exactly as $x_n$ but through $\sigma \circ \rho_O$, and $Y := \mathrm{pr}_\sigma^{-1}(W)$. The conclusion is that $x_n' \in \mathrm{pr}_\sigma^{-1}(W)$ and that there is a morphism $g : Y \to \operatorname{Spec}\bigl(O'[X_0,X_1]/(X_0X_1 - \sigma(p^e))\bigr)$ over $O'$ (its composite with the Spec of $O' \to$ the crossing quotient being $Y \hookrightarrow X_{O'} \to \operatorname{Spec} O'$) such that both coordinate classes lie in the prime $g(x_n')$, the stalk map of $g$ at $x_n'$ is flat, carries the maximal ideal onto the maximal ideal and induces an isomorphism of residue fields, and the germs at $x_n'$ of $\mathrm{pr}_\sigma^{*}g_u$ and $\mathrm{pr}_\sigma^{*}g_v$ coincide with the germs of the pullbacks along $g$ of the two coordinate classes of $O'[X_0,X_1]/(X_0X_1-\sigma(p^e))$.
--
--   This is the base-change step for the étale crossing chart of the Deligne–Rapoport model of $X_H(M)$ at a supersingular crossing: a chart over the coefficient ring $O$, with coordinates $uv = p^e$, is transported along $\sigma : O \to O'$ to an oriented chart at the corresponding crossing of the $O'$-model, with the two coordinates matching after pullback. It is used in [`ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart`](thm.html#ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart), where the completed local ring at the crossing is identified with a $uv$-model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_chart_baseChange_mem_and_flat_and_map_maximalIdeal_eq_and_isIso_residueFieldMap_and_germ_eq_of_chart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    letI bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
    letI prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    letI B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    letI W := U.ι ''ᵁ ⊤
    letI Y : Scheme.{0} := ↑(prσ ⁻¹ᵁ W)
    ∃ (hmem : xn' ∈ prσ ⁻¹ᵁ W)
      (g : Y ⟶ CrossingQuotient.crossingScheme (σ (((p : ℕ) : O) ^ e))),

      g ≫ Spec.map (CommRingCat.ofHom (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))) =
        (prσ ⁻¹ᵁ W).ι ≫ pullback.snd _ _ ∧

      (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal ∧ CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal) ∧

      ((g.stalkMap ⟨xn', hmem⟩).hom.Flat ∧
        Ideal.map (g.stalkMap ⟨xn', hmem⟩).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
        IsIso (g.residueFieldMap ⟨xn', hmem⟩)) ∧

      ((prσ ⁻¹ᵁ W).ι.stalkMap ⟨xn', hmem⟩).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ W) xn' hmem).hom ((prσ.app W).hom gu)) =
        (Y.presheaf.germ ⊤ ⟨xn', hmem⟩ trivial).hom
          ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e))))) ∧
      ((prσ ⁻¹ᵁ W).ι.stalkMap ⟨xn', hmem⟩).hom
          (((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ W) xn' hmem).hom ((prσ.app W).hom gv)) =
        (Y.presheaf.germ ⊤ ⟨xn', hmem⟩ trivial).hom
          ((g.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))).inv.hom (CrossingQuotient.V (σ (((p : ℕ) : O) ^ e))))) := by sorry
