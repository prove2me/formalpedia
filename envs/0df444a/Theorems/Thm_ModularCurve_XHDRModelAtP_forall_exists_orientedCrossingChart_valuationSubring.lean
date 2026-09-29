-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_orientedCrossingChart_valuationSubring
-- name    : ModularCurve.XHDRModelAtP.forall_exists_orientedCrossingChart_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/dfebf1ad-3570-51d1-beea-3c6bb6ba053a
-- title:
--   Oriented crossing charts over the valuation ring A
-- statement:
--   Fix a prime $p$ and $M$ with $p\mid M$ but $p^2\nmid M$, a subgroup $H\le(\mathbb Z/M)^\times$ containing every unit that becomes $1$ in $(\mathbb Z/(M/p))^\times$, and the hypothesis $hj$ that the $q$-expansion `jqModC ℚ` lies in the function field `qExpFunctionFieldC ℚ ⊤`; let $\mathfrak X$ be a term of the structure `XHDRModelAtP p M H hpM hj`, which packages a proper, flat, locally finitely presented integral two-chart model `X p (ΓM M H) hj` over $\operatorname{Spec}(R\,p)$ with normal affine sections, a smooth model at level `ΓN`, and a curve model over $\overline{\mathbb Q}$ identified with its generic base change. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, with residue field algebraically closed of characteristic $p$, and let $\rho\colon R\,p\to A$ be a ring map compatible with $R\,p\to\overline{\mathbb Q}$. Let $bc$ be a morphism from the fibre of the model over the residue field of $A$, along $(\mathrm{residue})\circ\rho$, to $\mathfrak X_A=\operatorname{pullback}$ of `toBase p (ΓM M H) hj` along $\operatorname{Spec}\rho$, compatible with the first projections and with the second projections up to $\operatorname{Spec}$ of the residue map. Then for every point $n$ of the fibre product of the two morphisms `𝔛.comp A hA ρ hρ 0` and `𝔛.comp A hA ρ hρ 1` into that special fibre — the crossings of the two components — there exist $e\ge 1$, an open subscheme $U$ of $\mathfrak X_A$ containing the image $x_n$ of $n$ under $\mathrm{pr}_1$ followed by `𝔛.comp … 0` and $bc$, and a morphism $f\colon U\to\operatorname{Spec}\bigl(A[X_0,X_1]/(X_0X_1-p^e)\bigr)$ such that: $f$ followed by $\operatorname{Spec}$ of the structure map $A\to A[X_0,X_1]/(X_0X_1-p^e)$ equals the inclusion of $U$ followed by the projection to $\operatorname{Spec}A$; for $y\in U$ both classes `CrossingQuotient.U` and `CrossingQuotient.V` of $p^e$ lie in the prime $f(y)$ exactly when $y$ maps to $x_n$; at every such $y$ the stalk map of $f$ is flat, pushes the maximal ideal onto the maximal ideal, and induces an isomorphism of residue fields; some open $W\subseteq U$ contains a point over $x_n$ and $W\hookrightarrow U$ followed by $f$ is étale; for $\tau$ in the inertia subgroup of the decomposition group of $A$ over $\mathbb Q$, and $x',y'\in A$ with $x'y'=p^e$ (hence also $\tau(x')\tau(y')=p^e$), any two sections $s,s'\colon\operatorname{Spec}A\to U$ of the structure morphism with $s'$ the $\tau$-transport of $s$ on the first projection satisfy: if $s$ followed by $f$ is $\operatorname{Spec}$ of `CrossingQuotient.lift x' y'`, then $s'$ followed by $f$ is $\operatorname{Spec}$ of the lift at $\tau(x'),\tau(y')$; and, in both directions, $y$ lies in the vanishing locus of $V$ precisely when its image lies in the image of `𝔛.comp … 0 ≫ bc`, and in that of $U$ precisely when its image lies in the image of `𝔛.comp … 1 ≫ bc`.
--
--   This is the crossing-chart description of the Deligne–Rapoport model of $X_H(M)$ at a prime $p$ exactly dividing $M$, in the form taken over the valuation ring $A$ of a place of $\overline{\mathbb Q}$ above $p$ rather than over an abstract discrete valuation ring: each crossing of the two components of the special fibre has an inertia-equivariant, oriented étale neighbourhood of the standard crossing $\operatorname{Spec}A[u,v]/(uv-p^e)$. It is obtained from the chart theorem over a discrete valuation ring together with the rationality of the crossings over the inertia field, and is used in the analysis of the component group and the local behaviour of the model at the crossings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_forall_exists_orientedCrossingChart_valuationSubring.lean

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

theorem ModularCurve.XHDRModelAtP.forall_exists_orientedCrossingChart_valuationSubring
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (bc : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶
      pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) :
    ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      ∃ (e : ℕ) (_ : 1 ≤ e)
        (U : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : ↥A) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥A (CrossingQuotient ↥A (((p : ℕ) : ↥A) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∃ W : (U : Scheme.{0}).Opens,
          (∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc).base n ∧ y ∈ W) ∧
          AlgebraicGeometry.Etale (W.ι ≫ f)) ∧

        (∀ (τ : ↥(A.decompositionSubgroup ℚ)), τ ∈ A.inertiaSubgroup ℚ →
          ∀ (x' y' : ↥A) (hxy : x' * y' = algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
            (hxy' : (MulSemiringAction.toRingHom _ (↥A) τ) x' * (MulSemiringAction.toRingHom _ (↥A) τ) y' =
              algebraMap ↥A ↥A (((p : ℕ) : ↥A) ^ e))
            (sU sU' : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
            sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
            sU' ≫ U.ι ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom _ (↥A) τ)) ≫ sU ≫ U.ι ≫ pullback.fst _ _ →
            sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e) x' y' hxy).toRingHom) →
            sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := ((p : ℕ) : ↥A) ^ e)
              ((MulSemiringAction.toRingHom _ (↥A) τ) x') ((MulSemiringAction.toRingHom _ (↥A) τ) y') hxy').toRingHom)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bc).base →
            CrossingQuotient.V (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bc).base →
            CrossingQuotient.U (((p : ℕ) : ↥A) ^ e) ∈ (f.base y).asIdeal) := by sorry
