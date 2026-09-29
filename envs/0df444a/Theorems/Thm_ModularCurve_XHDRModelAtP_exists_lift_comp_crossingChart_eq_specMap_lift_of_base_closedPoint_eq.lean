-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq
-- name    : ModularCurve.XHDRModelAtP.exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/94c9f373-5f07-5772-ad33-1979f922534d
-- title:
--   Section through a crossing factors through the crossing chart
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis $hj$ that the Laurent series `jqModC` $\mathbb{Q}$ lies in the intermediate field `qExpFunctionFieldC` $\mathbb{Q}$ $\top$ of $q$-expansions at level one; let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, i.e. a model of $X_H(M)$ over `R p` together with its listed properties. Let $A \subseteq \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map. Given a morphism $bc$ from the fibre of `toBase p (ΓM M H) hj` over the residue field of $A$ (via `residue` composed with $\rho$) to the base change $\mathcal{X}_A$ of the model along $\operatorname{Spec}\rho$, a point $n$ of the pullback of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1`, write $x_n$ for its image under the first projection followed by `𝔛.comp A hA ρ hρ 0` and $bc$. Given $e \in \mathbb{N}$, an open $U \subseteq \mathcal{X}_A$ containing $x_n$, and a morphism $f : U \to \operatorname{Spec}\bigl(A[X_0,X_1]/(X_0X_1 - p^e)\bigr)$ which is compatible with the projections to $\operatorname{Spec} A$ (that is, $f$ followed by $\operatorname{Spec}$ of the structure map equals $U.\iota$ followed by `pullback.snd`) and for which a point $y \in U$ satisfies that both coordinate classes `CrossingQuotient.U` and `CrossingQuotient.V` lie in the prime $f(y)$ exactly when $y$ maps to $x_n$; and given a section $sA : \operatorname{Spec} A \to \mathcal{X}_A$ of the projection to $\operatorname{Spec} A$ sending the closed point of $A$ to $x_n$. Then there exist $x', y' \in A$ with $x'y' = p^e$ and a morphism $sU : \operatorname{Spec} A \to U$ such that $x'$ and $y'$ lie in the maximal ideal of $A$, $sU$ followed by the open immersion $U.\iota$ equals $sA$, and $sU$ followed by $f$ equals $\operatorname{Spec}$ of the $A$-algebra homomorphism `CrossingQuotient.lift` $x'\,y'$ sending the two coordinates to $x'$ and $y'$. Only existence is asserted, not uniqueness of $(x',y')$.
--
--   This is the local description of an $A$-valued point of the Deligne–Rapoport model of $X_H(M)$ passing through an ordinary double point of the special fibre: in an oriented crossing chart $uv = p^e$ around the crossing, such a point acquires annulus coordinates $x', y' \in \mathfrak{m}_A$ with $x'y' = p^e$. It feeds the construction of the inertia line bundle attached to such points, being cited in the course of [`ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.exists_isInvertible_iso_ofPoint_tensor_idealModule_iso_tensorUnit_of_range_subset_range_comp_inter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing ModularCurve ModularCurve.XHDRLevel MvPolynomial
open scoped MatrixGroups

set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_lift_comp_crossingChart_eq_specMap_lift_of_base_closedPoint_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ)
    (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal ∧
        CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ↔
      U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n)

    (sA : Spec (CommRingCat.of ↥A) ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (hsA : sA ≫ pullback.snd _ _ = 𝟙 _)
    (hsn : sA.base (IsLocalRing.closedPoint ↥A) =
      (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n) :
    ∃ (x' y' : ↥A) (hxy : x' * y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
      (sU : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
      x' ∈ IsLocalRing.maximalIdeal ↥A ∧ y' ∈ IsLocalRing.maximalIdeal ↥A ∧
      sU ≫ U.ι = sA ∧
      sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom) := by sorry
