-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
-- name    : ModularCurve.XHDRModelAtP.hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/77165cf9-1680-50c2-8437-3f725e0a3c19
-- title:
--   Chart fraction at a crossing: common value on both branches
-- statement:
--   Fix a prime $p$ and a non-zero modulus $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial; assume the $q$-expansion `jqModC ℚ` lies in the level-$\top$ $q$-expansion function field over $\mathbb{Q}$, and let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : R_p \to A$ be a ring map compatible with the structure map to $\overline{\mathbb{Q}}$ and providing the $R_p$-algebra structure of $A$. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{F}_M =$ `xHFunctionFieldBar M H` pinned by the hypothesis that for any two $\overline{\mathbb{Q}}$-sections $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ with $y'$ followed by `𝔛.eeta`, the first pullback projection and `𝔛.w.hom` equal to $y$ followed by `𝔛.eeta` and that projection, the associated places satisfy $\mathrm{pointEquivPlace}(y') = \mathrm{ofAlgAut}(\theta) \cdot \mathrm{pointEquivPlace}(y)$. Let $\gamma$ be an injective ring homomorphism from $T = A \otimes_{R_p} \mathcal{O}(\text{$j$-finite chart at level } \Gamma_M(H))$ into $\overline{F}_M$ sending $a \otimes b$ to $a \cdot \mathrm{coeffEmb}(b)$ as Laurent series. Let $n$ be a point of the pullback of the two morphisms $\mathfrak{X}.\mathrm{comp}\,A\,\rho\,0$ and $\mathfrak{X}.\mathrm{comp}\,A\,\rho\,1$, let $\mathfrak{Q} \subseteq T$ be an ideal and $\chi_\kappa : T \to \kappa$ a ring homomorphism with kernel $\mathfrak{Q}$ restricting on the left factor to the residue map of $A$, and assume there is a morphism $t$ from $\mathrm{Spec}\,\kappa$ to the fibre of the model over $\mathrm{residue} \circ \rho$ whose first projection is $\mathrm{Spec}$ of $\chi_\kappa$ followed by $\mathrm{Spec}$ of the right inclusion and `ιFin`, whose second projection is the identity, and which carries the closed point of $\mathrm{Spec}\,\kappa$ to the image of $n$ under the first projection followed by $\mathfrak{X}.\mathrm{comp}\,A\,\rho\,0$. Then for every $h \in \overline{F}_M$ and all $a, c \in T$ with $c \notin \mathfrak{Q}$ and $h \cdot \gamma(c) = \gamma(a)$, both of the following hold: first, whenever $x, y$ are Laurent series over $A$ with non-zero reduction of $y$ to $\kappa$ and $h \cdot y = x$ holds after pushing $x, y$ forward into $\overline{\mathbb{Q}}$-Laurent series, every $g$ in `JHNeronObjectAtP.Fbar p M H hpM κ` with $g \cdot \bar y = \bar x$ lies in the valuation subring of the place $\mathfrak{X}.\mathrm{placeOn0}\,A\,\rho\,n$ with residue the image of $\chi_\kappa(a)/\chi_\kappa(c)$; second, the same conclusion with $h$ replaced by $\theta h$ and the place by $\mathfrak{X}.\mathrm{placeOn1}\,A\,\rho\,n$.
--
--   This is the evaluation clause of the branch dictionary at a supersingular crossing of the Deligne–Rapoport model of $X_H(M)$ over $R_p$: a fraction $a/c$ of chart functions which is regular at the crossing restricts to each of the two components through that point with one and the same value $\chi_\kappa(a)/\chi_\kappa(c)$, the two components being recorded by the places `placeOn0` (the Frobenius-twisted place attached to the node) and `placeOn1` (the node's place itself), and the Atkin–Lehner automorphism $\theta$ interchanging the two branches. It is used by [`ModularCurve.XHDRModelAtP.exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime`](thm.html#ModularCurve.XHDRModelAtP.exists_branch_primes_gauss_iff_and_hasValue_of_crossing_prime) and by [`ModularCurve.XHDRModelAtP.exists_snd_branch_prime_of_crossing_prime_of_regularProlongation`](thm.html#ModularCurve.XHDRModelAtP.exists_snd_branch_prime_of_crossing_prime_of_regularProlongation) in the construction of the crossing dictionary for the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
  ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.hasValue_placeOn0_and_placeOn1_of_mul_eq_of_not_mem_crossing_prime
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [Algebra (R p) ↥A] (halg : algebraMap (R p) ↥A = ρ)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (γ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ↥(xHFunctionFieldBar M H))
    (hγ : ∀ (a : ↥A) (b : ↥(chartAlgFin p (ΓM M H) hj)), ((γ (a ⊗ₜ b) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      (a : AlgebraicClosure ℚ) • coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)))
    (hγinj : Function.Injective γ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))

    (𝔔 : Ideal (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))) (χκ : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj)) →+* ResidueField ↥A)
    (hker : RingHom.ker χκ = 𝔔)
    (hχA : χκ.comp (Algebra.TensorProduct.includeLeftRingHom (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))) = IsLocalRing.residue ↥A)
    (ht : ∃ t : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom χκ) ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R p) (A := ↥A) (B := ↥(chartAlgFin p (ΓM M H) hj))).toRingHom) ≫
              ιFin p (ΓM M H) hj ∧
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0).base n)
    : ∀ (h : ↥(xHFunctionFieldBar M H)) (a c : (↥A ⊗[R p] ↥(chartAlgFin p (ΓM M H) hj))), c ∉ 𝔔 → h * γ c = γ a →
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn0 A hA ρ hρ n).HasValue g (χκ a / χκ c)) ∧
        (∀ (x y : LaurentSeries ↥A), coeffMap (IsLocalRing.residue ↥A) y ≠ 0 →
          ((θ h : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
          ∀ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), (g : LaurentSeries (ResidueField ↥A)) * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x →
            (𝔛.placeOn1 A hA ρ hρ n).HasValue g (χκ a / χκ c)) := by sorry
