-- Prove2me | Theorems.Thm_ModularCurve_natCard_torsion_eq_pow_card_ssPlacesQExp_sub_one_mul_natCard_finPts_of_abelJacobiPin_tauFree
-- name    : ModularCurve.natCard_torsion_eq_pow_card_ssPlacesQExp_sub_one_mul_natCard_finPts_of_abelJacobiPin_tauFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/82d5f132-923b-5291-b0cf-a9908de829e4
-- title:
--   Index of the finite part in J_H(M)[p] for p ‖ M
-- statement:
--   Fix a prime $p$ with $p \neq 2$, a non-zero modulus $M$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ whose hypothesis `hHp` requires that every unit of $\mathbb{Z}/M$ mapping to $1$ under the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ lies in $H$. A set $S$ of natural numbers is also fixed. The predicate `hin` is the package `HeckeDiamondInputsHAll M H`: for every prime $\ell$ the data `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ at level $(M,H)$ and $\ell$, and for every $d \in (\mathbb{Z}/M)^\times$ an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of the function field $F_H =$ `xHFunctionFieldBar M H` with `IsDiamondAutHBar M H d σ`. Further fixed are a valuation subring $\mathfrak{P}$ of $\overline{\mathbb{Q}}$ with $p$ in its set of non-units (`LiesOverPrime p`), whose residue field is algebraically closed of characteristic $p$; an algebraically closed field $K$ which is an algebra over $\mathbb{Z}/p$; and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the full-level $q$-expansion function field `qExpFunctionFieldC ℚ ⊤`.
--
--   The geometric frame consists of: an integral model datum $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` for $X_H$ over the localisation `R p`, which in particular provides a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ of $F_H$ (a proper smooth integral curve together with a bijection `placeOfPoint` between its closed points and the places of $F_H$) and an isomorphism $\mathfrak{X}.\mathrm{eeta}$ of $\mathfrak{X}.\mathrm{Meta}.C$ with the geometric generic fibre; level data $\Lambda :$ `JHNeronObjectAtP.LevelData p M H hpM 𝔓` (a lift $\sigma_A$ of the geometric generic point to $\operatorname{Spec}\mathfrak{P}$, a scheme with relative group law over the base, and parametrisations of its generic and special sections by $J_H(M/p)$ at the image level subgroup and by $\mathrm{Pic}^0$ of the residue-field function field); the hypothesis `hrepΛ` that the relative $\mathrm{Pic}^0$ designation built from $\Lambda.X$, $\Lambda.f$ and the identity section of $\Lambda.L$ represents the `algEquivZeroCut` subfunctor of the rigidified relative Picard functor of `toBase p (ΓN p M H hpM) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ followed by $\mathfrak{X}.\pi$; and a Néron object $O :$ `JHNeronObjectAtP p M H hpM 𝔓 hPl Λ`, that is, a smooth separated group scheme $O.G \to$ `base p` with commutative relative group law $O.L$, a bijection $O.\mathrm{pts} : J_H(M) \simeq$ sections over the geometric generic point, Hecke endomorphisms, and a toric rank $O.\mathrm{toricRank}$.
--
--   The Abel–Jacobi pinning consists of the following hypotheses, whose long categorical shapes are summarised here. `hD` states that the designation $(O.G, O.g, \text{unit of } O.L)$ represents the `algEquivZeroCut` condition for `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$, and `hDQ` the same statement after base change of both the curve and the designation to $\mathbb{Q}$; `hsep` asserts that the base change of `toBase p (ΓM M H) hj` to $\mathbb{Q}$ is separated. A section $\mathrm{aj}_{\mathbb{Q}}$ of the base-changed designation over the base-changed curve is given, together with: `hpoinc`, an isomorphism between the Poincaré bundle of `hDQ` and the base change to $\mathbb{Q}$ of the Poincaré bundle of `hD` pulled back along the first projection of $O.g$; `hajQε`, which says that $\mathrm{aj}_{\mathbb{Q}}$ precomposed with the base-changed rigidifying section is the zero section; and `hajQ`, the Abel–Jacobi property of $\mathrm{aj}_{\mathbb{Q}}$: for every field $K'$, every point $t : \operatorname{Spec} K' \to \operatorname{Spec}\mathbb{Q}$ and every $K'$-point $x$ of the base-changed curve, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $\mathrm{aj}_{\mathbb{Q}}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the base point $t$ followed by the base-changed rigidifying section. A morphism $k_{\mathbb{Q}}$ from the geometric generic fibre to the generic fibre is given, compatible with both projections via `hkQ₁` and `hkQ₂` (the second up to the map $\operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Q}$). A morphism $\overline{\mathrm{aj}} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ is defined by `hajbar` as $\mathfrak{X}.\mathrm{eeta}$ followed by $k_{\mathbb{Q}}$, by $\mathrm{aj}_{\mathbb{Q}}$ and by the first projection of $O.g$, and lies over the base by `hajbar_over`. A geometric point $\overline{\varepsilon}$ of $\mathfrak{X}.\mathrm{Meta}.C$ is given which corresponds to $\mathfrak{X}.\varepsilon_{\inf}$ (`hεbar`) and is sent by $\overline{\mathrm{aj}}$ to the identity section of $O.L$ (`hεbar_aj`). Finally `hpts_law` states that $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` through `algEquivZeroGroupCut`, and `hAJ` states that for all geometric points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ with $s$ corresponding to $\mathfrak{X}.\varepsilon_{\inf}$ there is a degree-zero divisor $D_v$ on $F_H$ equal to $[\text{place of } x] - [\text{place of } s]$ with $(O.\mathrm{pts}(\,\mathrm{cl}\,D_v))_1 = x$ followed by $\overline{\mathrm{aj}}$.
--
--   The inertia ring is a commutative domain $R$ which is a Henselian local ring with algebraically closed residue field, equipped with an algebra structure on $\overline{\mathbb{Q}}$ for which scalar multiplication is faithful, subject to: `hRA`, the image of $R$ in $\overline{\mathbb{Q}}$ lies in $\mathfrak{P}$; `hRdvr`, $R$ is a discrete valuation ring; `hRirr`, $p$ is irreducible in $R$; `hRfix`, an automorphism $\sigma$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lies in the inertia subgroup of $\mathfrak{P}$ over $\mathbb{Q}$ precisely when it fixes the image of $R$ pointwise; and `hRmax`, every element of $\mathfrak{P}$ fixed by that inertia subgroup lies in the image of $R$.
--
--   The finite-part layer is a $p$-divisible group $\mathcal{G} :$ [`PDivisibleGroup R p h`](def/PDivisibleGroup_Basic.html#L199) of height $h$ over $R$ (levels $\mathcal{G}.\mathrm{level}\,v$ finite free cocommutative Hopf $R$-algebras of rank $p^{vh}$, with surjective transition maps whose kernels are the $p^v$-torsion ideals), together with an additive map $\Delta$ from the group $\mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}})$ — the direct limit of the level-$v$ point groups — to $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, F_H)$, subject to four hypotheses: `hΔinj`, $\Delta$ is injective; `hΔlev`, for every $v$ an element $y$ of $J_H(M)$ lies in $O.\mathrm{finPts}(p^v)$ — the subgroup generated by the $p^v$-torsion classes $x$ for which the section $O.\mathrm{pts}\,x$ extends over $\operatorname{Spec}\mathfrak{P}$ along $\Lambda.\sigma_A$ — if and only if $y$ is the image under $\Delta$ of (the class of) a level-$v$ point of $\mathcal{G}$ over $\overline{\mathbb{Q}}$; `hΔgal`, for $\tau \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and an $R$-algebra automorphism $\tau'$ of $\overline{\mathbb{Q}}$ agreeing with $\tau$, $\Delta(\tau' \cdot z) = \tau \cdot \Delta z$ for all $z$; and `hΔhecke`, for every set $S$ of natural numbers and every generator $g :$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) there is a family of coalgebra-algebra endomorphisms $\varphi_v$ of the levels commuting with the transition maps such that precomposition by $\varphi_v$ on level-$v$ points corresponds under $\Delta$ to the operator `genOpH M H S g` on $J_H(M)$ (the Hecke operator $T_\ell$ or $U_q$, or the diamond operator, according to the generator).
--
--   Two numerical hypotheses are imposed: `hrank1`, that the $p$-torsion subgroup of $\mathrm{Pic}^0(\overline{\mathbb{Q}}, F_H)$ has cardinality $p^{h + O.\mathrm{toricRank}}$; and `htK`, that the set `ssPlacesQExp K (GammaH (M/p) (infSubgroup p M H hpM)) p` — the places of the $q$-expansion function field over $K$ at level $\Gamma_{H'}(M/p)$, $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, satisfying the predicate `IsSSPlaceQExp` — has cardinality $O.\mathrm{toricRank} + 1$.
--
--   The conclusion is the single equality
--   $$\#\,\mathrm{Pic}^0(\overline{\mathbb{Q}}, F_H)[p] \;=\; p^{\,\#\mathrm{ssPlacesQExp} - 1} \cdot \#\{x \in \mathrm{Pic}^0(\overline{\mathbb{Q}}, F_H)[p] \;:\; x \in O.\mathrm{finPts}\,p\},$$
--   where the exponent is the cardinality of the place set of `htK` minus one and the second factor counts the elements of the $p$-torsion subgroup whose underlying class lies in $O.\mathrm{finPts}\,p$. Equivalently, in view of `hrank1` and `htK`, the finite part of the $p$-torsion has order $p^h$ and index $p^{O.\mathrm{toricRank}}$.
--
--   This is the counting form, at a prime $p$ exactly dividing the level $M$, of the statement that the finite (connected, $p$-divisible) part of $J_H(M)[p]$ has order $p^h$ and index $p^{t}$, with $t$ the toric rank, equal to one less than the number of supersingular places at level $M/p$. It is used downstream, in the construction of a reduced root function via the $d\log$ argument, where the index computation is what makes the relevant residue map surjective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_natCard_torsion_eq_pow_card_ssPlacesQExp_sub_one_mul_natCard_finPts_of_abelJacobiPin_tauFree.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open ModularCurve in

theorem ModularCurve.natCard_torsion_eq_pow_card_ssPlacesQExp_sub_one_mul_natCard_finPts_of_abelJacobiPin_tauFree
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]

    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (R : Type) [CommRing R] [IsDomain R] [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Algebra R (AlgebraicClosure ℚ)] [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R) (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ} (𝒢 : PDivisibleGroup R p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H)
    (hΔinj : Function.Injective Δ)
    (hΔlev : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (hΔgal : ∀ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ' : AlgebraicClosure ℚ ≃ₐ[R] AlgebraicClosure ℚ),
      (∀ x : AlgebraicClosure ℚ, τ' x = τ x) →
      ∀ z : 𝒢.Points (AlgebraicClosure ℚ), Δ (τ' • z) = τ • Δ z)
    (hΔhecke : ∀ (S : Set ℕ) (g : CohCarrier.Gen M S), ∃ φ : ∀ v : ℕ, 𝒢.level v →ₐc[R] 𝒢.level v,
        (∀ v : ℕ, (𝒢.transition v).comp (φ (v + 1)) = (φ v).comp (𝒢.transition v)) ∧
        ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul (PDivisibleGroup.Point.ofAlgHom
            ((PDivisibleGroup.Point.toAlgHom x).comp (φ v : 𝒢.level v →ₐ[R] 𝒢.level v))))) =
            ModularCurve.genOpH M H S g (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x))))

    (hrank1 : Nat.card ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) = p ^ (h + O.toricRank))

    (htK : Nat.card ↥(ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) = O.toricRank + 1)
    :
    Nat.card ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) =
      p ^ (Nat.card ↥(ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) - 1) * Nat.card {x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) // ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∈ O.finPts p} := by sorry
