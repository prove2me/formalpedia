-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart
-- name    : ModularCurve.XHDRModelAtP.exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/247c3ed3-e04e-5088-aeb2-d10ce023921a
-- title:
--   Hensel lifting of A-points on the étale crossing chart
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction along $M/p \mid M$ is trivial; assume the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`, and let $\mathfrak{X}$ be a term of `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of an algebraic closure of $\mathbb{Q}$ with $p$ a non-unit of $A$, whose residue field has characteristic $p$ and is algebraically closed, and let $\rho : R_p \to A$ be a ring homomorphism inducing the structure map $R_p \to \overline{\mathbb{Q}}$. Let $O$ be a discrete valuation domain with $\mathfrak{m}_O = (p)$, equipped with $\rho_O : R_p \to O$, a map $\mathrm{to}\kappa : O \to \kappa_A$ with $\mathrm{to}\kappa \circ \rho_O = \mathrm{res}_A \circ \rho$, a map $j_O : O \to \overline{\mathbb{Q}}$ over $R_p$, and $\iota_A : O \to A$ inducing $j_O$ and $\mathrm{to}\kappa$. Let $n$ be a point of the fibre product of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` into the fibre of the model over $\kappa_A$, and write $x_n$ for the image of $n$ in $X_O = X \times_{\operatorname{Spec} R_p} \operatorname{Spec} O$ under the first projection followed by `𝔛.comp A hA ρ hρ 0` and by `bcMap`. Let $e \ge 1$, let $U$ be an open of $X_O$ containing $x_n$, and let $f : U \to \operatorname{Spec}\bigl(O[X_0,X_1]/(X_0X_1 - p^e)\bigr)$ be a morphism over $\operatorname{Spec} O$, i.e. $f$ followed by the Spec of the structure map equals the inclusion $U \hookrightarrow X_O$ followed by the projection to $\operatorname{Spec} O$. Assume: both `CrossingQuotient.U (p^e)` and `CrossingQuotient.V (p^e)` lie in the prime $f(y)$ exactly when $y$ maps to $x_n$; at every $y$ over $x_n$ the stalk map of $f$ is flat, carries the maximal ideal onto the maximal ideal, and induces an isomorphism of residue fields; every such $y$ has an open neighbourhood $V \subseteq U$ with $V \hookrightarrow U$ followed by $f$ étale; and the two branches are oriented, in the sense that `CrossingQuotient.V (p^e)` lies in $f(y)$ if and only if $y$ maps into the image of `𝔛.comp A hA ρ hρ 0` composed with `bcMap`, and `CrossingQuotient.U (p^e)` lies in $f(y)$ if and only if $y$ maps into the image of the analogous morphism with index $1$. The conclusion: for every ring homomorphism $\chi : O[X_0,X_1]/(X_0X_1 - p^e) \to A$ restricting to $\iota_A$ on $O$ and sending both `CrossingQuotient.U (p^e)` and `CrossingQuotient.V (p^e)` into $\mathfrak{m}_A$, there is a morphism $s : \operatorname{Spec} A \to U$ such that $s$ followed by $U \hookrightarrow X_O$ and the projection to $\operatorname{Spec} O$ is $\operatorname{Spec}(\iota_A)$, the image in $X_O$ of the closed point of $A$ under $s$ is $x_n$, and $s$ followed by $f$ is $\operatorname{Spec}(\chi)$.
--
--   This is the existence half of the parametrisation of $A$-points through a crossing point of the special fibre by the local model $uv = p^e$: every admissible pair of values in $\mathfrak{m}_A$ is realised by a section of the étale chart passing through the crossing. It rests on henselianity of the valuation ring of an algebraically closed field, via [`ValuationSubring.henselianLocalRing_of_isAlgClosed`](thm.html#ValuationSubring.henselianLocalRing_of_isAlgClosed), and on the existence of sections of étale morphisms over henselian local bases with separably closed residue field, via [`AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing`](thm.html#AlgebraicGeometry.exists_section_base_closedPoint_eq_of_etale_of_henselianLocalRing). It is used in the construction of the annulus coordinate at a crossing and in the associated statement about units and vanishing orders read off the chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart.lean

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

theorem ModularCurve.XHDRModelAtP.exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart
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
    ∀ χ : CrossingQuotient O (((p : ℕ) : O) ^ e) →+* ↥A,
      χ.comp (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e))) = ιA →
      χ (CrossingQuotient.U (((p : ℕ) : O) ^ e)) ∈ IsLocalRing.maximalIdeal ↥A →
      χ (CrossingQuotient.V (((p : ℕ) : O) ^ e)) ∈ IsLocalRing.maximalIdeal ↥A →
      ∃ s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}),
        s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) ∧
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∧
        s ≫ f = Spec.map (CommRingCat.ofHom χ) := by sorry
