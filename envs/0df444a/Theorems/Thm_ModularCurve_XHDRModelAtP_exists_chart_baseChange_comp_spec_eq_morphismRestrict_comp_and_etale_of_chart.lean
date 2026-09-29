-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
-- name    : ModularCurve.XHDRModelAtP.exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/cd7a51de-8417-5da1-a5b4-8b0304c78e24
-- title:
--   Base change of the crossing chart along O → O'
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, and a subgroup $H \leq (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$; fix the hypothesis `hj` that `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, and a model package $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` for the two-chart integral model `X p (ΓM M H) hj` over `R p`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit, whose residue field is algebraically closed of characteristic $p$, and $\rho : R_p \to A$ inducing the structure map to $\overline{\mathbb{Q}}$. Let $O$ be a discrete valuation ring with maximal ideal $(p)$, $\rho_O : R_p \to O$, and compatible maps $\mathrm{to}\kappa : O \to \kappa(A)$, $j_O : O \to \overline{\mathbb{Q}}$ and $\iota_A : O \to A$ lifting $j_O$ and inducing $\mathrm{to}\kappa$. Write $X_O :=$ `XO (ΓM M H) hj ρO`, the pullback of `toBase p (ΓM M H) hj` along $\operatorname{Spec}\rho_O$. Let $n$ be a point of the fibre product of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` into the fibre of the model over $\kappa(A)$, and let $x_n \in X_O$ be the image of $n$ under the first projection followed by the branch `0` and by `bcMap`. Assume $e \geq 1$, an open $U \subseteq X_O$ with $x_n \in U$, and a morphism $f : U \to \operatorname{Spec} O[X_0,X_1]/(X_0X_1 - p^e)$ whose composite with $\operatorname{Spec}$ of the structure map $O \to O[X_0,X_1]/(X_0X_1-p^e)$ is the inclusion of $U$ followed by the projection to $\operatorname{Spec} O$, subject to: the vertex condition that both coordinate classes $u, v$ lie in $f(y)$ exactly when $y$ lies over $x_n$; at each $y$ over $x_n$, flatness of the stalk map of $f$, the image of the maximal ideal generating the maximal ideal, and an isomorphism on residue fields; étaleness of $f$ on some open neighbourhood of each such $y$; and the branch conditions that $v \in f(y)$ holds exactly when $y$ lies in the image of the branch `0` composed with `bcMap`, and $u \in f(y)$ exactly when $y$ lies in the image of the branch `1`. Let further $O'$ be a discrete valuation ring, $\sigma : O \to O'$, and $\iota_{A'} : O' \to A$ injective and local with $\iota_{A'} \circ \sigma = \iota_A$, together with $j_{O'} : O' \to \overline{\mathbb{Q}}$ satisfying the evident compatibilities with $\sigma \circ \rho_O$, $A \hookrightarrow \overline{\mathbb{Q}}$ and the residue map of $A$. Set $X_{O'} :=$ `XO (ΓM M H) hj (σ.comp ρO)`, let $\mathrm{pr}_\sigma : X_{O'} \to X_O$ be the map induced by $\sigma$, let $x_n' \in X_{O'}$ be the point obtained from $n$ as above but with the base-change map `bc'` over $O'$, and let $W$ be the image of $U$ under its inclusion. Then $x_n' \in \mathrm{pr}_\sigma^{-1}(W)$, one has $\mathrm{pr}_\sigma^{-1}(W) = \mathrm{pr}_\sigma^{-1}(U)$, and there exist a ring map $\psi : O[X_0,X_1]/(X_0X_1-p^e) \to O'[X_0,X_1]/(X_0X_1-\sigma(p^e))$ with $\psi \circ (O \to \cdot) = (O' \to \cdot) \circ \sigma$, $\psi(u) = u$, $\psi(v) = v$, and a morphism $g : \mathrm{pr}_\sigma^{-1}(W) \to \operatorname{Spec} O'[X_0,X_1]/(X_0X_1-\sigma(p^e))$ over $\operatorname{Spec} O'$ such that $g$ followed by $\operatorname{Spec}\psi$ equals the transport along the above equality of opens followed by the restriction $\mathrm{pr}_\sigma|_U$ and then $f$, both coordinate classes lie in the prime $g(x_n')$, and some open $V' \subseteq \mathrm{pr}_\sigma^{-1}(W)$ contains $x_n'$ with the inclusion of $V'$ followed by $g$ étale. The statement also fixes notation for the generic fibre over $\overline{\mathbb{Q}}$ and its projections to $X_O$ and $X_{O'}$, for the stalk of $X_{O'}$ at $x_n'$ as an $O'$-algebra, and for the pullbacks under $f$ of the two coordinates.
--
--   This is the base-change step for the étale crossing charts of the integral model of $X_H(M)$ at $p$: a chart $f$ presenting a neighbourhood of a supersingular crossing point as étale over $\operatorname{Spec} O[u,v]/(uv-p^e)$ is carried along a local map $\sigma : O \to O'$ of discrete valuation rings inside $A$ to a chart $g$ over $O'[u,v]/(uv-\sigma(p^e))$, compatibly with $f$ via the coordinate-preserving map $\psi$. It is used by the companion statement recording flatness, the maximal-ideal and residue-field conditions, and the germ identities for the chart over $O'$ at the crossing point $x_n'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart.lean

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

theorem ModularCurve.XHDRModelAtP.exists_chart_baseChange_comp_spec_eq_morphismRestrict_comp_and_etale_of_chart
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
    ∃ (hmem : xn' ∈ prσ ⁻¹ᵁ W) (hWU : prσ ⁻¹ᵁ W = prσ ⁻¹ᵁ U)
      (ψ : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* CrossingQuotient O' (σ (((p : ℕ) : O) ^ e)))
      (g : Y ⟶ CrossingQuotient.crossingScheme (σ (((p : ℕ) : O) ^ e))),

      ψ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e)))).comp σ ∧
      ψ (CrossingQuotient.U (((p : ℕ) : O) ^ e)) = CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) ∧ ψ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) = CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) ∧

      g ≫ Spec.map (CommRingCat.ofHom (algebraMap O' (CrossingQuotient O' (σ (((p : ℕ) : O) ^ e))))) = (prσ ⁻¹ᵁ W).ι ≫ pullback.snd _ _ ∧

      g ≫ Spec.map (CommRingCat.ofHom ψ) = ((XO (ΓM M H) hj (σ.comp ρO)).isoOfEq hWU).hom ≫ (prσ ∣_ U) ≫ f ∧

      (CrossingQuotient.U (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal ∧ CrossingQuotient.V (σ (((p : ℕ) : O) ^ e)) ∈ (g.base ⟨xn', hmem⟩).asIdeal) ∧

      ∃ V' : Y.Opens, (⟨xn', hmem⟩ : ↥Y) ∈ V' ∧ Etale (V'.ι ≫ g) := by sorry
