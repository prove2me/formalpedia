-- Prove2me | Theorems.Thm_ModularCurve_exists_pDivisibleGroup_raynaudQuotient_toricPts_finitePart_jHNeronObjectAtP_of_closedImmersion
-- name    : ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_finitePart_jHNeronObjectAtP_of_closedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/69ee97d6-1c32-55ab-bc6e-770976e920c4
-- title:
--   Raynaud quotient of the finite part by its toric subgroup
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the whole kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`), with $M/p$ nonzero. Fix further a valuation subring $Pl$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `Pl.LiesOverPrime p`, i.e. the image of $p$ lies in the non-units of $Pl$, whose residue field is of characteristic $p$ and algebraically closed, and a witness `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`. The base throughout is $\operatorname{Spec}$ of $R_p =$ `R p`, the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$.
--
--   The geometric input consists of: a model datum $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) (properness, flatness, integrality, finite presentation, normality of the $\Gamma_M$-model, properness and relative smoothness of dimension $1$ of the $\Gamma_N$-model, a curve model over $\overline{\mathbb{Q}}$ identified with the generic geometric fibre together with its Galois and $q$-expansion compatibilities, and further clauses, summarised here); a level datum $\Lambda$ (a scheme $\Lambda.X$ over `base p` with a relative group law $\Lambda.L$, a section $\Lambda.\sigma_A$ over $Pl$ lifting the generic point, and dictionaries for its generic and special points); and an object $O$ of type [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), that is a scheme $O.G$ with structure morphism $O.g$ to `base p`, a commutative relative group law $O.L$, a bijection $O.\mathrm{pts}$ from $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_{M,H})$ onto the sections over the generic point which is additive and Galois-equivariant, smoothness, separatedness, local finiteness of type, quasi-compactness, surjectivity and fibrewise preconnectedness of $O.g$, Hecke correspondences, flatness and surjectivity of multiplication by $n>0$, and a toric rank $O.\mathrm{toricRank}$, among other clauses summarised here. Two representability hypotheses are imposed: `hrep` asserts that $O.G$ with structure map $O.g$ and zero section the unit of $O.L$ represents the subfunctor of the relative Picard functor of the $\Gamma_M$-model `toBase p (ΓM M H) hj`, rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, cut out by the condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero of the rigidified line bundle over all algebraically closed fields); `hrepΛ` asserts the analogous representability of $\Lambda.X$, $\Lambda.f$ with the unit of $\Lambda.L$ as zero section, for the $\Gamma_N$-model `toBase p (ΓN p M H hpM) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$.
--
--   The local input is a henselian local domain $R_h$, equipped with an algebra structure over which $\overline{\mathbb{Q}}$ is faithful, such that `hRA`: every element of $R_h$ maps into $Pl$, and `hRloc`: an element of $R_h$ lies in the maximal ideal exactly when the $Pl$-valuation of its image is $<1$. Over $R_h$ a $p$-divisible group $\mathcal{G}$ of height $h$ is given: a family of finite free cocommutative Hopf $R_h$-algebras $\mathcal{G}.\mathrm{level}\,v$ of rank $p^{vh}$, with surjective transition bialgebra maps $\mathcal{G}.\mathrm{level}(v+1) \to \mathcal{G}.\mathrm{level}\,v$ whose kernels are the $p^v$-torsion ideals. A ring homomorphism $\rho_h : R_p \to R_h$ is given with `hρh`: composing it with $R_h \to \overline{\mathbb{Q}}$ gives the structure map $R_p \to \overline{\mathbb{Q}}$.
--
--   The embedding data are morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$ subject to: `hιbase`, $\iota_v$ followed by $O.g$ equals $\operatorname{Spec}$ of $R_h \to \mathcal{G}.\mathrm{level}\,v$ followed by $\operatorname{Spec} \rho_h$; `hιcl`, the resulting morphism into the fibre product of $O.g$ and $\operatorname{Spec}\rho_h$ is a closed immersion; `hιp`, $\iota_v$ followed by the multiplication-by-$p^v$ endomorphism $O.L.\mathrm{schemeNsmul}(p^v)$ agrees with $\iota_v \circ$ (structure map) followed by the unit section, so the image is killed by $p^v$; `hιmul`, for every $v$, every commutative $R_h$-algebra $B$ and all $B$-points $x,y$ of $\mathcal{G}$ at level $v$ lying over the structure map (hypotheses $hx$, $hy$), the morphism attached to the convolution product $x\cdot y$ followed by $\iota_v$ is the $O.L$-product of the two corresponding sections, so that $\iota$ is a homomorphism on points; `hιt`, $\operatorname{Spec}$ of the transition map followed by $\iota_{v+1}$ equals $\iota_v$; and `hιfin`, for every $v$, writing $K_v$ for the $p^v$-kernel, the pullback of $O.L.\mathrm{schemeNsmul}(p^v)$ along the unit section, and $j_v$ for the induced morphism from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ to the fibre product of $K_v \to$ `base p` with $\operatorname{Spec}\rho_h$, the morphism $j_v$ is both an open and a closed immersion, and every point of that fibre product lying over the closed point of $R_h$ belongs to the range of $j_v$.
--
--   Finally, a points dictionary is given: an additive map $\Delta$ from $\mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}})$, the direct limit of the level point groups, to $J_H(M)$, with `hΔinj` injectivity; `hΔlev`, for every $v$ an element $y$ of $J_H(M)$ lies in $O.\mathrm{finPts}(p^v)$ (the subgroup generated by the $p^v$-torsion classes whose section $O.\mathrm{pts}$ extends to the place in the sense of `ExtendsToPlace` for $Pl$ and $\Lambda.\sigma_A$) if and only if $y = \Delta(x)$ for some level-$v$ point $x$; `hΔgal`, for $\tau \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and an $R_h$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$ agreeing with $\tau$ pointwise, $\Delta(\tau' \cdot z) = \tau \cdot \Delta(z)$; `htor`, every element of $O.\mathrm{toricPts}(p^v)$ (the subgroup generated by the range of $O.\mathrm{toricPoint}(p^v)$) is $\Delta$ of a level-$v$ point; and `hιpts`, the section attached by $O.\mathrm{pts}$ to $\Delta(x)$ for a level-$v$ point $x$ is $\operatorname{Spec}$ of the algebra homomorphism of $x$ followed by $\iota_v$.
--
--   Under these hypotheses there exist a natural number $h_B$, a $p$-divisible group $\mathcal{B}$ over $R_h$ of height $h_B$ for the same prime $p$, a family of $R_h$-bialgebra maps $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$, and a natural number $h'$, such that all of the following hold:
--
--   (i) $h = O.\mathrm{toricRank} + h_B$;
--
--   (ii) $h_B = 2h'$, so $h_B$ is even;
--
--   (iii) for every $v$, the transition map of $\mathcal{G}$ composed after $\psi_{v+1}$ equals $\psi_v$ composed after the transition map of $\mathcal{B}$;
--
--   (iv) for every $v$ and every $\overline{\mathbb{Q}}$-point $x$ of $\mathcal{G}$ at level $v$, the $\overline{\mathbb{Q}}$-point of $\mathcal{B}$ at level $v$ obtained from the algebra homomorphism of $x$ precomposed with $\psi_v$ is the identity point (the unit of the convolution group) if and only if $\Delta(x)$ lies in $O.\mathrm{toricPts}(p^v)$;
--
--   (v) for every $v$ and every $\overline{\mathbb{Q}}$-point $b$ of $\mathcal{B}$ at level $v$ there is a $\overline{\mathbb{Q}}$-point $x$ of $\mathcal{G}$ at level $v$ whose image under precomposition with $\psi_v$ is $b$, so the induced map on $\overline{\mathbb{Q}}$-points is surjective at each level;
--
--   (vi) for every $v$ and every $\overline{\mathbb{Q}}$-point $x$ of $\mathcal{G}$ at level $v$: if the associated point of $\mathcal{B}$ reduces to the identity at the place, in the sense that for every $a \in \mathcal{B}.\mathrm{level}\,v$ the $Pl$-valuation of the difference between its value at $a$ and the image of the counit of $a$ is $<1$, then the same holds for $x$ itself, i.e. for every $a \in \mathcal{G}.\mathrm{level}\,v$ the $Pl$-valuation of the value of $x$ at $a$ minus the image of the counit of $a$ is $<1$.
--
--   This is the Raynaud-quotient step for the finite part at $p$ of the Néron object of $J_H(M)$: the toric points are divided out of the $p$-divisible group $\mathcal{G}$ attached to the finite part, yielding a $p$-divisible group of even height $h - O.\mathrm{toricRank}$ whose points at each level are exactly the quotient of those of $\mathcal{G}$ by the toric subgroup, together with the reflection of reduction to the identity at the place. It is a weakening of the companion statement [`ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion`](thm.html#ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_and_exists_retraction_finitePart_jHNeronObjectAtP_of_closedImmersion), which in addition produces a retraction, and it is used in the assembly of the finite part in [`ModularCurve.exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic`](thm.html#ModularCurve.exists_pDivisibleGroup_points_eq_finPts_raynaudExtension_closedImmersion_jHNeronObjectAtP_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pDivisibleGroup_raynaudQuotient_toricPts_finitePart_jHNeronObjectAtP_of_closedImmersion.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.exists_pDivisibleGroup_raynaudQuotient_toricPts_finitePart_jHNeronObjectAtP_of_closedImmersion
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)
    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιfin : ∀ (v : ℕ)
      (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
      (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
          (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
        Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      let jv := pullback.lift
        (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
        (g := Spec.map (CommRingCat.ofHom ρh))
        (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
      IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
      ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
              (Spec.map (CommRingCat.ofHom ρh))),
        (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
          x ∈ Set.range jv.base)

    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    :
    ∃ (hB : ℕ) (ℬ : PDivisibleGroup Rh p hB) (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v) (h' : ℕ),
      h = O.toricRank + hB ∧
      hB = 2 * h' ∧
      (∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v)) ∧
      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v)) ∧
      (∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b) ∧
      (∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1)) := by sorry
