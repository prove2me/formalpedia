-- Prove2me | Theorems.Thm_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv
-- name    : ModularCurve.reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/7d39d536-f23a-5080-846c-bd3ab4355b2f
-- title:
--   Reduced root function of T_ℓ x and U_q x as a norm
-- statement:
--   Fix a prime $p \neq 2$ and a level $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial, and a set $S$ of natural numbers. The hypothesis `hin` is the predicate [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the Hecke inputs `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ at level $(M,H)$ and $\ell$ hold, and for every $d \in (\mathbb{Z}/M)^\times$ there is a $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{\mathbb{Q}}F_H(M)$ realising the diamond operator $\langle d\rangle$ in the sense of `IsDiamondAutHBar`. Further data: a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ is a non-unit of $Pl$), whose residue field is algebraically closed of characteristic $p$; an algebraically closed field $K$ of characteristic $p$; and the hypothesis `hj` that the $q$-expansion [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) of $j$ lies in the function field `qExpFunctionFieldC ℚ ⊤`.
--
--   The geometric input consists of a model $\mathfrak{X}$ of type [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81) — an integral, proper, flat model of $X_H(M)$ over $R_p$ with the auxiliary level-$\Gamma_N$ model, together with a curve model `𝔛.Meta` of $\overline{\mathbb{Q}}F_H(M)$ over $\overline{\mathbb{Q}}$, the isomorphism `𝔛.eeta` onto the geometric fibre, the Galois compatibility of places, the pinning of the finite chart and the smoothness and geometric integrality of the generic fibre; level data $\Lambda$ of type [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32) (a section $\sigma_A$ over the base with $\bar{\sigma}_A$ the generic point, a scheme $X \to \operatorname{Spec} R_p$ with a relative group law and bijections of $J_H(M/p)$-points and of special-fibre $\mathrm{Pic}^0$-points with sections); the hypothesis `hrepΛ` that the Poincaré-type datum built from $\Lambda.X$, $\Lambda.f$ and the identity section represents the relative sub-Picard functor cut out by the fibrewise algebraically-equivalent-to-zero condition for the level-$\Gamma_N$ model; and a Néron object $O$ of type [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), i.e. a smooth separated group scheme $g : G \to \operatorname{Spec} R_p$ with relative commutative group law, a bijection $O.\mathrm{pts} : J_H(M) \simeq$ sections over the generic point compatible with addition, Galois action and Hecke operators, and the usual flatness, surjectivity, properness and fibre-connectivity clauses.
--
--   The representability and abel–Jacobi block consists of: `hD`, asserting that $(O.G, O.g, \text{unit section})$ represents the relative sub-Picard functor for the $\Gamma_M$-model with the algebraically-equivalent-to-zero cut; `hDQ`, the same statement after base change to $\mathbb{Q}$; `hsep`, separatedness of the base-changed curve over $\mathbb{Q}$; a section `ajQ` of the base-changed curve over the base of the base-changed designation; a morphism `kQ` between the geometric and the $\mathbb{Q}$-fibre of the $\Gamma_M$-model; a morphism `ajbar : 𝔛.Meta.C ⟶ O.G`; a $\overline{\mathbb{Q}}$-point `εbar` of `𝔛.Meta.C` over the base; `hpoinc`, an isomorphism between the Poincaré bundle of `hDQ` and the base change to $\mathbb{Q}$ of the pullback of the Poincaré bundle of `hD` along the first projection of $O.g$; `hajQε`, saying that the base-changed unit section followed by `ajQ` is the zero section; `hajQ`, the defining property of `ajQ` as an Abel–Jacobi map: for every field $K'$, every morphism $t$ from $\operatorname{Spec} K'$ to $\operatorname{Spec}\mathbb{Q}$ and every point $x$ of the base-changed curve over $t$, the pullback of the `hDQ` Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the relative effective Cartier divisor of $t$ followed by the base-changed unit section; `hkQ₁` and `hkQ₂`, the two compatibilities of `kQ` with the projections (the second involving $\operatorname{Spec}$ of $\mathbb{Q} \to \overline{\mathbb{Q}}$); `hajbar`, identifying `ajbar` with `𝔛.eeta` followed by `kQ`, `ajQ` and the first projection of $O.g$; `hajbar_over`, saying `ajbar` lies over the generic point; `hεbar` and `hεbar_aj`, placing `εbar` over the unit section of $\mathfrak{X}$ and over the identity of the group law; `hpts_law`, that $O.\mathrm{pts}$ is additive for the relative group law determined by `hD`; and `hAJ`, asserting that for all $\overline{\mathbb{Q}}$-points $x, s$ of `𝔛.Meta.C` over the base with $s$ lying over the unit section there is a degree-zero divisor $Dv$ on $\overline{\mathbb{Q}}F_H(M)$ equal to the difference of the places of $x$ and of $s$ with $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of } Dv)$ given by $x$ followed by `ajbar`.
--
--   The local ring block introduces a domain $R$ which is a Henselian local ring with algebraically closed residue field, an $R$-algebra structure on $\overline{\mathbb{Q}}$ with faithful scalar action, and: `hRA`, that $R$ maps into $Pl$; `hRdvr`, that $R$ is a discrete valuation ring; `hRirr`, that $p$ is irreducible in $R$; `hRfix`, that an automorphism $\sigma$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ lies in the inertia subgroup of $Pl$ exactly when it fixes the image of $R$ pointwise; and `hRmax`, that every element of $Pl$ fixed by that inertia subgroup comes from $R$.
--
--   The $p$-divisible group block introduces $h \in \mathbb{N}$, a $p$-divisible group $\mathcal{G}$ of height $h$ over $R$ (levels with Hopf algebra structures, surjective transitions, prescribed ranks $p^{vh}$ and kernel of transition equal to the $p^v$-torsion ideal), an additive map $\Delta$ from the $\overline{\mathbb{Q}}$-points of $\mathcal{G}$ to $J_H(M)$, with: `hΔinj`, injectivity of $\Delta$; `hΔlev`, that for every $v$ an element $y$ of $J_H(M)$ lies in $O.\mathrm{finPts}(p^v)$ — the subgroup generated by the $p^v$-torsion classes whose section extends over $\Lambda.\sigma_A$ — exactly when $y$ is $\Delta$ of the image of some level-$v$ point; `hΔgal`, that $\Delta$ is equivariant for automorphisms $\tau$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ which are $R$-linear; and `hΔhecke`, that for every set $S$ and every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) there is a compatible family of coalgebra endomorphisms $\varphi_v$ of the levels of $\mathcal{G}$ commuting with the transitions and inducing, via $\Delta$, the operator `genOpH M H S g` on $J_H(M)$.
--
--   The Atkin–Lehner block introduces a semilinear automorphism `wgen` of $\overline{\mathbb{Q}}F_H(M)$ over $\overline{\mathbb{Q}}$ with `hwgen`: whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of `𝔛.Meta.C` satisfy $y'$ followed by `𝔛.eeta` and the first projection and $\mathfrak{X}.w$ equals $y$ followed by `𝔛.eeta` and the first projection, then the place of $y'$ is `wgen` applied to the place of $y$. It further introduces a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $\overline{\mathbb{Q}}F_H(M)$ with `hθ`: whenever $f$ at level $(M,H)$ and $u$ at level $(M/p, \mathrm{infSubgroup}\,p\,M\,H)$ have equal Laurent expansions, the expansion of $\theta f$ is [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25) of that of $u$ with parameter $p$, that is $u(q^p)$; and `hwθ`, that `wgen` is the semilinear automorphism `SemilinearAut.ofAlgAut θ`.
--
--   Finally, a ring homomorphism $\iota_K : Pl \to K$ with `hιK`, that $\iota_K(y) = 0$ precisely when the valuation of $y$ is $< 1$ (reduction modulo the maximal ideal), and a map
--   $$\Psi : \mathrm{Pic}^0(\overline{\mathbb{Q}}F_H(M))[p] \to \mathrm{qExpFunctionFieldC}\,K\,\Gamma_H(M/p, \mathrm{infSubgroup}\,p\,M\,H)$$
--   subject to `hΨ`: for every $p$-torsion class $x$ there exist a degree-zero divisor $D$, a non-zero $f \in \overline{\mathbb{Q}}F_H(M)$ and a Laurent series $y$ with coefficients in $Pl$ such that the class of $D$ is $x$, the divisor of $f$ equals $p$ times the `wgen`-translate of $D$ place by place, the Laurent expansion of $f$ is that of $y$ pushed into $\overline{\mathbb{Q}}$, the reduction of $y$ modulo the maximal ideal of $Pl$ is non-zero, and the Laurent expansion of $\Psi x$ is $\iota_K$ applied coefficientwise to $y$.
--
--   Under these hypotheses the conclusion is a conjunction of two statements.
--
--   First: for every prime $\ell$ with $\ell \notin S$ and $\ell \nmid M$, and all $p$-torsion classes $x, y$ such that $y = T_\ell x$ in $J_H(M)$, where $T_\ell$ is [`ModularCurve.genOpH M H S`](def/ModularCurve_XHOperators.html#L80) applied to the generator `CohCarrier.Gen.T ℓ hℓ hℓS hℓM`, there exist $c \in K$ and an element $g$ of $\mathrm{qExpFunctionFieldC}\,K\,\Gamma_H(M/p,\mathrm{infSubgroup}\,p\,M\,H)$ with $c \neq 0$ and
--   $$\Psi y = c \cdot g^{p} \cdot N\bigl(\beta_\ell(\Psi x)\bigr),$$
--   where $\beta_\ell$ is [`ModularCurve.heckeBetaModLH K (M/p) (infSubgroup p M H hpM) ℓ`](def/ModularCurve_XHDifferentialsModL.html#L167) into the level $\Gamma_H(M/p) \cap \Gamma_0((M/p)\ell)$ field and $N$ is the `Algebra.norm` taken for the algebra structure supplied by [`ModularCurve.heckeAlphaModLH K (M/p) (infSubgroup p M H hpM) ℓ`](def/ModularCurve_XHDifferentialsModL.html#L132), the inclusion of the level-$\Gamma_H(M/p)$ field into that field.
--
--   Second: for every prime $q'$ with $q' \mid M$ and $q' \neq p$, and all $p$-torsion classes $x, y$ such that $y = U_{q'} x$ in $J_H(M)$, where $U_{q'}$ is [`ModularCurve.genOpH M H S`](def/ModularCurve_XHOperators.html#L80) applied to `CohCarrier.Gen.U q' hq hqM`, there exist $c \in K$, $c \neq 0$, and $g$ in the same field with
--   $$\Psi y = c \cdot g^{p} \cdot N\bigl(\beta_{q'}(\Psi x)\bigr),$$
--   with $\beta_{q'}$ and the norm along $\alpha_{q'}$ formed at level $(M/p, \mathrm{infSubgroup}\,p\,M\,H)$ and parameter $q'$ exactly as in the first conjunct.
--
--   This is the Hecke-equivariance statement for the reduced root function attached to the $p$-torsion of $J_H(M)$ in the Ribet level-lowering argument: the reduction modulo $p$ of the $p$-th root of the $w$-translated divisor of a $p$-torsion class transforms, under $T_\ell$ for $\ell \nmid M$ and under $U_{q'}$ for $q' \mid M$, $q' \neq p$, into the norm along the first degeneracy map of the $\beta$-image, up to a constant and a $p$-th power. It feeds the construction of the map from $p$-torsion to polar differentials used in the analysis of the special fibre at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv.lean

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

theorem ModularCurve.reducedRootFunction_genOpH_T_eq_smul_pow_mul_norm_heckeBetaModLH_of_abelJacobiPin_tauFree_of_algEquiv
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

    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)
    :
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.T ℓ hℓ hℓS hℓM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ (Ψ x)))) ∧
    (∀ (q' : ℕ) (hq : q'.Prime) (hqM : q' ∣ M) (_ : q' ≠ p) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.U q' hq hqM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p *
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero q' := ⟨hq.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * q'))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q').toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) q' (Ψ x)))) := by sorry
