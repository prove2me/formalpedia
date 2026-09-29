-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_comp_eq_specMap_and_mem_maximalIdeal_and_mul_eq_of_section_of_chart
-- name    : ModularCurve.XHDRModelAtP.exists_comp_eq_specMap_and_mem_maximalIdeal_and_mul_eq_of_section_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/1b537a34-6324-5f56-b0f8-4ff48ed7d9cc
-- title:
--   Crossing coordinates of an A-section through the node
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that is trivial modulo $M/p$, and $hj$ expressing that $j$, as a $q$-expansion, lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$; let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit, with algebraically closed residue field of characteristic $p$, let $\rho : R_p \to A$ be compatible with $R_p \to \overline{\mathbb{Q}}$, let $O$ be a discrete valuation domain with $\mathfrak{m}_O = (p)$ and $\rho_O : R_p \to O$, and let $\mathrm{to}\kappa$, $j_O$, $\iota_A$ be maps out of $O$ to the residue field of $A$, to $\overline{\mathbb{Q}}$ and to $A$, compatible with $\rho$, $\rho_O$ and with each other as stated. Let $n$ be a point of the fibre product of the two maps $\mathfrak{X}.\mathrm{comp}\,0$ and $\mathfrak{X}.\mathrm{comp}\,1$, and write $x_n$ for its image in the $O$-model $\mathrm{XO}$ under the first projection followed by $\mathfrak{X}.\mathrm{comp}\,0$ followed by `bcMap`. Let $e \ge 1$, let $U$ be an open of $\mathrm{XO}$ containing $x_n$, and let $f : U \to \operatorname{Spec} O[u,v]/(uv - p^e)$ be a morphism over $\operatorname{Spec} O$ (that is, $f$ followed by the structure map equals $U.\iota$ followed by the projection to $\operatorname{Spec} O$) such that: a point of $U$ lies over the vertex, i.e. both coordinates `CrossingQuotient.U` and `CrossingQuotient.V` lie in its prime, exactly when it maps to $x_n$; at every point over $x_n$ the stalk map is flat, carries the maximal ideal onto the maximal ideal and induces an isomorphism of residue fields, and $f$ is étale on some neighbourhood; and the vanishing of `CrossingQuotient.V` (resp. `CrossingQuotient.U`) at a point of $U$ is equivalent to that point lying in the image of the first (resp. second) component. Then for every $s : \operatorname{Spec} A \to U$ with $s$ followed by $U.\iota$ and the projection to $\operatorname{Spec} O$ equal to $\operatorname{Spec}(\iota_A)$, and whose closed point is sent to $x_n$: there is a ring homomorphism $\chi : O[u,v]/(uv-p^e) \to A$ with $s$ followed by $f$ equal to $\operatorname{Spec}(\chi)$, and every such $\chi$ satisfies $\chi \circ (O \to O[u,v]/(uv-p^e)) = \iota_A$, $\chi(\mathtt{U}), \chi(\mathtt{V}) \in \mathfrak{m}_A$, and $\chi(\mathtt{U})\,\chi(\mathtt{V}) = \iota_A(p^e)$.
--
--   This is the valuation-theoretic reading of a node on the Deligne–Rapoport style model: an $A$-valued section passing through the crossing point $x_n$ has both crossing-chart coordinates in the maximal ideal of $A$, with product exactly $p^e$, so that the section lands in the annulus $|p^e| < |\chi(\mathtt{V})| < 1$ attached to the node. It feeds the annulus-parametrisation and chart-reading results for the crossing frame, where the coordinate values are converted into valuations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_comp_eq_specMap_and_mem_maximalIdeal_and_mul_eq_of_section_of_chart.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP MvPolynomial
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_comp_eq_specMap_and_mem_maximalIdeal_and_mul_eq_of_section_of_chart
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
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    ∀ s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
      s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (∃ χ : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* ↥A, s ≫ f = Spec.map (CommRingCat.ofHom χ)) ∧
      ∀ χ : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* ↥A, s ≫ f = Spec.map (CommRingCat.ofHom χ) →
        χ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = ιA ∧
        χ (CrossingQuotient.U (((p : ℕ) : O) ^ e)) ∈ IsLocalRing.maximalIdeal ↥A ∧
        χ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) ∈ IsLocalRing.maximalIdeal ↥A ∧
        χ (CrossingQuotient.U (((p : ℕ) : O) ^ e)) * χ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) = ιA (((p : ℕ) : O) ^ e) := by sorry
