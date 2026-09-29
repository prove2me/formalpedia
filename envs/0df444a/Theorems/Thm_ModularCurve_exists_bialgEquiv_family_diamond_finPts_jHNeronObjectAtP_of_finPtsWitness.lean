-- Prove2me | Theorems.Thm_ModularCurve_exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness
-- name    : ModularCurve.exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/34a777b9-7643-56eb-9a59-8cd62f5e14e6
-- title:
--   Diamond operator ⟨ d⟩ as an automorphism of the finite part
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`). Fix a valuation subring $Pl$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, in the sense that $p$ is a non-unit of $Pl$ (`hPl`), whose residue field is of characteristic $p$ and algebraically closed. Assume `hj`, namely that the $q$-expansion [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) of $j$ lies in the field [`ModularCurve.qExpFunctionFieldC ℚ ⊤`](def/ModularCurve_X1.html#L101) generated over $\mathbb{Q}$ by the level-one intermediate-form ratios. The geometric data consist of: a model $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81), packaging the two-chart integral models $X$ of level $\Gamma_M$ and of level $\Gamma_N$ over the ring $R_p =$ [`ModularCurve.XHDRLevel.R p`](def/ModularCurve_XHDRModelAtP.html#L22) together with their properness, flatness, normality and smoothness properties, a curve model $M_\eta$ for the function field $\overline{\mathbb{Q}}$-curve of $X_H$, the cusp section $\mathfrak{X}.\varepsilon_\infty$ and the level map $\mathfrak{X}.\pi$; level data $\Lambda$ of type [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32), consisting of a lift $\sigma_A$ of the base point, a scheme $\Lambda.X$ over `base p` with a relative group law $\Lambda.L$ and identifications of the degree-zero divisor class group at level $M/p$ and of the special-fibre $\mathrm{Pic}^0$ with the sections of $\Lambda.f$; and a Néron object $O$ of type [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), i.e. a smooth separated surjective group scheme $O.g : O.G \to$ `base p` with commutative relative group law $O.L$, an identification $O.\mathrm{pts}$ of $J_H(M) =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) (the degree-zero divisor class group `Pic0` of the base-changed function field `xHFunctionFieldBar M H`) with the sections of $O.g$ over the generic point, compatible with addition, with the Galois action and with the Hecke generators $O.\mathrm{hecke}\,S\,g$, together with flatness and surjectivity of multiplication by $n$, properness of the generic fibre, a toric rank $O.\mathrm{toricRank}$ and the remaining fields of that structure.
--
--   Two representability hypotheses are imposed. The hypothesis `hrep` asserts that the type of `RepresentsRelSubPic` data is non-empty for the level-$\Gamma_M$ integral model `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_\infty$, for the sub-Picard condition `algEquivZeroCut` (whose predicate selects those rigidified line bundles that are algebraically equivalent to zero on every geometric fibre), and for the designation whose total space is $O.G$, whose structure morphism is $O.g$ and whose zero section is the unit of $O.L$ at the identity of $\operatorname{Spec} R_p$; such a datum consists of a Poincaré rigidified bundle satisfying the condition, its universal property, and triviality of its pullback along the zero section. The hypothesis `hrepΛ` is the analogous assertion for the level-$\Gamma_N$ model `toBase p (ΓN p M H hpM) hj`, rigidified along the composite of $\mathfrak{X}.\varepsilon_\infty$ with $\mathfrak{X}.\pi$, and for the designation built from $\Lambda.X$, $\Lambda.f$ and the unit of $\Lambda.L$.
--
--   The Henselian base consists of a commutative domain $R_h$ that is a Henselian local ring, equipped with an $R_h$-algebra structure on $\overline{\mathbb{Q}}$ with injective structure map, such that $R_h$ maps into $Pl$ (`hRA`) and such that an element of $R_h$ lies in the maximal ideal exactly when its image has $Pl$-valuation $< 1$ (`hRloc`). A set $S \subseteq \mathbb{N}$ and a unit $d \in (\mathbb{Z}/M)^\times$ are fixed.
--
--   The main datum is a $p$-divisible group $\mathcal{G}$ over $R_h$ of height $h$: a system of finite free cocommutative Hopf $R_h$-algebras $\mathcal{G}.\mathrm{level}\,v$ with surjective transition bialgebra maps, $R_h$-rank $p^{vh}$ at level $v$, and kernel of the $v$-th transition equal to the $p^v$-torsion ideal. It comes with an additive map $\Delta$ from the direct limit $\mathcal{G}.\mathrm{Points}\,\overline{\mathbb{Q}}$ of the groups of $\overline{\mathbb{Q}}$-points to $J_H(M)$, and a $\mathbb{Z}_p$-linear map $e$ between the associated Tate modules (Tate modules being the groups of sequences $(x_n)$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$).
--
--   The hypotheses on $(\Delta, e)$ are: `hΔinj`, injectivity of $\Delta$; `hΔlev`, that for all $v$ an element $y \in J_H(M)$ lies in $O.\mathrm{finPts}(p^v)$ — the subgroup generated by the $p^v$-torsion classes whose associated section satisfies the extension predicate `ExtendsToPlace` for $Pl$ and $\Lambda.\sigma_A$ — exactly when $y = \Delta(x)$ for some level-$v$ point $x$; `hΔgal`, that $\Delta$ is equivariant for any $\tau \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and any $R_h$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$ agreeing with $\tau$ pointwise; `hΔhecke`, that for every set $S'$ and every generator $g$ of [`CohCarrier.Gen M S'`](def/CohCarrier_Inst.html#L13) (a Hecke operator $T_\ell$, $U_q$ or a diamond $\langle d' \rangle$) there is a family of $R_h$-bialgebra endomorphisms $\varphi_v$ of the levels, commuting with the transitions, such that $\Delta$ carries the induced action on level-$v$ points to the operator [`ModularCurve.genOpH M H S' g`](def/ModularCurve_XHOperators.html#L80) on $J_H(M)$; `he`, that $e$ is computed coordinatewise by $\Delta$; `heinj`, injectivity of $e$; `herange`, that a Tate vector $y$ lies in the range of $e$ exactly when $y_n \in O.\mathrm{finPts}(p^n)$ for all $n$; `hegal`, that $e$ intertwines the Galois representation on $\mathcal{G}$'s Tate module with [`ModularCurve.JH.tateGaloisRep`](def/ModularCurve_XH.html#L154); `hsat`, that the range of $e$ is $p$-saturated; `hcoker`, that the cokernel of $e$ is $\mathbb{Z}_p$-linearly isomorphic to $\mathbb{Z}_p^{O.\mathrm{toricRank}}$; and `htor`, that every element of $O.\mathrm{toricPts}(p^v)$ (the subgroup generated by the toric points of $O$ at level $p^v$) is of the form $\Delta(x)$ for a level-$v$ point $x$.
--
--   A second $p$-divisible group $\mathcal{B}$ over $R_h$ of height $h_B$ is given, together with levelwise $R_h$-bialgebra maps $\psi_v : \mathcal{B}.\mathrm{level}\,v \to \mathcal{G}.\mathrm{level}\,v$, a natural number $h'$, and the hypotheses: `hhB`, $h = O.\mathrm{toricRank} + h_B$; `hhB2`, $h_B = 2h'$; `hψt`, compatibility of $\psi$ with the transitions; `hψker`, that a level-$v$ point of $\mathcal{G}$ has trivial image under $\psi_v$ exactly when its $\Delta$-image lies in $O.\mathrm{toricPts}(p^v)$; `hψsurj`, that every level-$v$ point of $\mathcal{B}$ arises from a level-$v$ point of $\mathcal{G}$ by composition with $\psi_v$; `hψred`, that if the $\psi_v$-image of a level-$v$ point $x$ reduces to the identity, in the sense that $Pl$-valuation of $x(\psi_v(a)) - \varepsilon(a)$ is $< 1$ for all $a$ (where $\varepsilon$ is the counit), then the same holds for $x$ itself on $\mathcal{G}.\mathrm{level}\,v$; and `hperiod`, that for every $v$, every $\sigma$ in the inertia subgroup of $Pl$ over $\mathbb{Q}$, every $p^v$-torsion class $z$ in $\mathrm{Pic}^0$ of `xHFunctionFieldBar M H`, and every level-$v$ point $y$ with $\Delta(y) = \sigma \cdot z - z$, the $\psi_v$-image of $y$ reduces to the identity in the above sense.
--
--   Finally, the $p$-divisible group is tied to the Néron object by a ring homomorphism $\rho_h : R_p \to R_h$ and morphisms $\iota_v : \operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v) \to O.G$, subject to: `hρh`, that $\rho_h$ followed by the structure map $R_h \to \overline{\mathbb{Q}}$ is the structure map of $R_p$; `hιbase`, that $\iota_v$ followed by $O.g$ equals $\operatorname{Spec}$ of $R_h \to \mathcal{G}.\mathrm{level}\,v$ followed by $\operatorname{Spec} \rho_h$; `hιcl`, that the resulting morphism to the fibre product of $O.g$ and $\operatorname{Spec}\rho_h$ is a closed immersion; `hιp`, that $\iota_v$ followed by multiplication by $p^v$ for $O.L$ factors through the unit section; `hιpts`, that the section attached by $O.\mathrm{pts}$ to $\Delta(x)$, for $x$ a level-$v$ point, is $\operatorname{Spec}$ of the algebra map of $x$ followed by $\iota_v$; `hιmul`, that for every $R_h$-algebra $B$ and level-$v$ points $x, y$ over $B$ whose associated morphisms lie over the base (as recorded by the two side conditions) the morphism attached to $x y$ is the $O.L$-product of the morphisms attached to $x$ and $y$; `hιt`, that $\operatorname{Spec}$ of the transition followed by $\iota_{v+1}$ equals $\iota_v$; `hιhecke`, that for every set $S'$ and generator $g$ of [`CohCarrier.Gen M S'`](def/CohCarrier_Inst.html#L13) there is a family of $R_h$-bialgebra endomorphisms $\varphi_v$ of the levels, commuting with the transitions, such that $\operatorname{Spec}\varphi_v$ followed by $\iota_v$ equals $\iota_v$ followed by the morphism $O.\mathrm{hecke}\,S'\,g$, and such that the induced maps on level-$v$ points correspond under $\Delta$ to [`ModularCurve.genOpH M H S' g`](def/ModularCurve_XHOperators.html#L80); and `hιfin`, that for every $v$ the comparison morphism $j_v$ from $\operatorname{Spec}(\mathcal{G}.\mathrm{level}\,v)$ into the fibre product, over $\operatorname{Spec}\rho_h$, of the kernel of multiplication by $p^v$ (the fibre product of $O.L$-multiplication by $p^v$ and the unit section) with $\operatorname{Spec} R_h$ — formed from the two factorisation hypotheses `h3` and `h4` — is both an open and a closed immersion, and that every point of that fibre product lying over the closed point of $R_h$ belongs to the image of $j_v$.
--
--   Under these hypotheses there exists a family of $R_h$-bialgebra automorphisms $D_p(v)$ of $\mathcal{G}.\mathrm{level}\,v$, one for each $v \in \mathbb{N}$, such that: first, for every $v$ the composite of $D_p(v+1)$ with the transition $\mathcal{G}.\mathrm{transition}\,v$ equals the composite of that transition with $D_p(v)$, as bialgebra maps $\mathcal{G}.\mathrm{level}(v+1) \to \mathcal{G}.\mathrm{level}\,v$; and second, for every $v$ the morphism $\operatorname{Spec}$ of (the ring homomorphism underlying) $D_p(v)$ followed by $\iota_v$ equals $\iota_v$ followed by the morphism underlying $O.\mathrm{hecke}\,S\,\langle d \rangle$, for the fixed $S$ and the diamond generator `CohCarrier.Gen.dia d`.
--
--   This realises the diamond operator $\langle d \rangle$ on the finite ($p$-divisible) part of the Néron object of $J_H(M)$ at $p$ as a transition-compatible family of bialgebra automorphisms of the levels, intertwined with the Hecke morphism on the Néron object. It is the first existential datum used in [`ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins`](thm.html#ModularCurve.exists_twoStepTower_raynaudQuotient_descent_finPts_jHNeronObjectAtP_of_finPtsWitness_of_bridgePins), in the analysis of the local behaviour at $p$ of the $p$-divisible group attached to the Jacobian, for the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
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

theorem ModularCurve.exists_bialgEquiv_family_diamond_finPts_jHNeronObjectAtP_of_finPtsWitness
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
    (S : Set ℕ) (d : (ZMod M)ˣ)

    {h : ℕ}
    (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (e : TateModule p (𝒢.Points (AlgebraicClosure ℚ)) →ₗ[ℤ_[p]] TateModule p (ModularCurve.JH M H))
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
    (he : ∀ (x : TateModule p (𝒢.Points (AlgebraicClosure ℚ))) (n : ℕ),
      ((e x : TateModule p (ModularCurve.JH M H)) : ℕ → ModularCurve.JH M H) n =
        Δ ((x : ℕ → 𝒢.Points (AlgebraicClosure ℚ)) n))
    (heinj : Function.Injective e)
    (herange : ∀ y : TateModule p (ModularCurve.JH M H), y ∈ LinearMap.range e ↔
      ∀ n : ℕ, (y : ℕ → ModularCurve.JH M H) n ∈ O.finPts (p ^ n))
    (hegal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[Rh] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ x : TateModule p (𝒢.Points (AlgebraicClosure ℚ)),
        e (𝒢.tateModuleRep (AlgebraicClosure ℚ) τ' x) = ModularCurve.JH.tateGaloisRep M H p τ (e x))
    (hsat : ∀ y : TateModule p (ModularCurve.JH M H), (p : ℤ_[p]) • y ∈ LinearMap.range e → y ∈ LinearMap.range e)
    (hcoker : Nonempty ((TateModule p (ModularCurve.JH M H) ⧸ LinearMap.range e) ≃ₗ[ℤ_[p]] (Fin O.toricRank → ℤ_[p])))
    (htor : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.toricPts (p ^ v) →
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    {hB : ℕ}
    (ℬ : PDivisibleGroup Rh p hB)
    (ψ : ∀ v : ℕ, ℬ.level v →ₐc[Rh] 𝒢.level v)
    {h' : ℕ}
    (hhB : h = O.toricRank + hB)
    (hhB2 : hB = 2 * h')
    (hψt : ∀ v : ℕ, (𝒢.transition v).comp (ψ (v + 1)) = (ψ v).comp (ℬ.transition v))
    (hψker : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) =
          (1 : ℬ.Point (AlgebraicClosure ℚ) v) ↔
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) ∈ O.toricPts (p ^ v))
    (hψsurj : ∀ (v : ℕ) (b : ℬ.Point (AlgebraicClosure ℚ) v), ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v,
      PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v)) = b)
    (hψred : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom x).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1) →
      (∀ a : 𝒢.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom x a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (hperiod : ∀ (v : ℕ), ∀ σ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ z ∈ AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) (p ^ v),
      ∀ y : 𝒢.Point (AlgebraicClosure ℚ) v,
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul y)) = σ • z - z →
        (∀ a : ℬ.level v, Pl.valuation (PDivisibleGroup.Point.toAlgHom (PDivisibleGroup.Point.ofAlgHom ((PDivisibleGroup.Point.toAlgHom y).comp (ψ v : ℬ.level v →ₐ[Rh] 𝒢.level v))) a -
          algebraMap Rh (AlgebraicClosure ℚ) (Coalgebra.counit a)) < 1))
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh)
    (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hρh : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hιbase : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hιcl : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
      IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
        (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hιp : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hιpts : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
      (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
        Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hιmul : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
      (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
      (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
      Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
        (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hιt : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)
    (hιhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (φ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v = ι v ≫ (O.hecke S g).1) ∧
      ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
        Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
          ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[Rh] 𝒢.level v))))) =
          ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))
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
    :
    ∃ Dp : ∀ v : ℕ, 𝒢.level v ≃ₐc[Rh] 𝒢.level v,
      (∀ v : ℕ, (𝒢.transition v).comp (Dp (v + 1) : 𝒢.level (v + 1) →ₐc[Rh] 𝒢.level (v + 1)) =
        (Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v).comp (𝒢.transition v)) ∧
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom ((Dp v : 𝒢.level v →ₐc[Rh] 𝒢.level v) : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
        ι v ≫ (O.hecke S (CohCarrier.Gen.dia d)).1) := by sorry
