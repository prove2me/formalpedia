-- Prove2me | Theorems.Thm_ModularCurve_exists_reducedRootFunction_torsion_mem_finPts_iff_forall_dvd_ord_of_abelJacobiPin_tauFree_of_algEquiv
-- name    : ModularCurve.exists_reducedRootFunction_torsion_mem_finPts_iff_forall_dvd_ord_of_abelJacobiPin_tauFree_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/238f02e0-0c37-593f-a1f9-94187e605555
-- title:
--   Reduced p-th root functions detect the finite part of J_H(M)[p]
-- statement:
--   Fix an odd prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the kernel of the reduction map $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ (hypothesis `hHp`). A set $S$ of natural numbers is among the data; it does not occur in the conclusion. The hypothesis `hin` is [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the Hecke input conditions `HeckeInputsHAlong` hold for $(M, H, \ell)$ over $\overline{\mathbb{Q}}$, and for every $d \in (\mathbb{Z}/M)^\times$ there is an $\overline{\mathbb{Q}}$-algebra automorphism of the geometric function field $\overline{\mathbb{Q}}(X_H(M))$ realising the diamond operator $\langle d\rangle$.
--
--   A place above $p$ is fixed: a valuation subring $Pl$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ (`Pl.LiesOverPrime p`), whose residue field is of characteristic $p$ and algebraically closed. Furthermore $K$ is an algebraically closed field which is an algebra over $\mathbb{F}_p$, and $\iota_K : Pl \to K$ is a ring homomorphism whose kernel is exactly the maximal ideal, in the form: $\iota_K(y) = 0$ if and only if the valuation of $y$ is $< 1$ (hypothesis `hιK`).
--
--   Geometric model and Néron object. The hypothesis `hj` asserts that the $q$-expansion `jqModC ℚ` of the modular invariant lies in the field `qExpFunctionFieldC ℚ ⊤`; $\mathfrak{X}$ is a [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81), i.e. a two-chart integral model of $X_H(M)$ over the base ring `R p` together with a curve model $\mathfrak{X}.\mathrm{Meta}$ of the geometric function field $\overline{\mathbb{Q}}(X_H(M))$ (`xHFunctionFieldBar M H`), its identification $\mathfrak{X}.\mathrm{eeta}$ with the generic geometric fibre, the section $\mathfrak{X}.\varepsilon_\infty$ at the cusp $\infty$, the Atkin–Lehner isomorphism $\mathfrak{X}.w$, and the usual properness, flatness, normality and smoothness data. The datum $\Lambda$ is a [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32) (a structure morphism $\sigma_{Pl}$ lifting the geometric generic point, a scheme $\Lambda.X$ over `base p` with a relative group law $\Lambda.L$, and bijections of its generic and special points with $J_{H'}(M/p)$ and with $\mathrm{Pic}^0$ of the reduced function field), and `hrepΛ` asserts that the designation formed from $\Lambda.X$, $\Lambda.f$ and the unit section of $\Lambda.L$ represents the rigidified line bundles on the level-$\Gamma_N$ model which are fibrewise algebraically equivalent to zero, relative to the section obtained by composing $\mathfrak{X}.\varepsilon_\infty$ with $\mathfrak{X}.\pi$. The object $O$ is a [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53): a smooth, separated, surjective group scheme $O.G \to$ `base p` with relative group law $O.L$, a bijection $O.\mathrm{pts}$ of $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{\mathbb{Q}}(X_H(M)))$ with its generic points, Galois- and Hecke-equivariance, and the further Néron-model properties recorded in that structure.
--
--   Abel–Jacobi pinning. A long group of hypotheses ties $O$ to the model $\mathfrak{X}$ through the relative Picard functor; its members are: `hD` and `hDQ`, that the designation built from $O.G$, $O.g$ and the unit section of $O.L$ represents the fibrewise-algebraically-trivial rigidified bundles for $(\mathfrak{X}, \varepsilon_\infty)$ over `R p` and, after base change, over $\mathbb{Q}$; `hsep`, separatedness of the generic fibre; `ajQ`, a section over the generic fibre into the base of the base-changed designation, with `hajQε` identifying its restriction along the cusp with the zero section, and `hajQ` the Abel–Jacobi property of `ajQ`, namely that for every field $K$, every point $t$ of $\operatorname{Spec}\mathbb{Q}$ with values in $K$ and every $t$-point $x$ of the curve, the pullback of the Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the cusp; `hpoinc`, that the Poincaré bundle of `hDQ` is isomorphic to the base change to $\mathbb{Q}$ of the pullback of the Poincaré bundle of `hD` along the first projection; `kQ` together with `hkQ₁`, `hkQ₂`, a comparison morphism between the geometric and the $\mathbb{Q}$-rational fibres compatible with both projections; $\overline{\mathrm{aj}}$ and `hajbar`, `hajbar_over`, exhibiting the geometric Abel–Jacobi morphism $\mathfrak{X}.\mathrm{Meta}.C \to O.G$ as $\mathfrak{X}.\mathrm{eeta}$ followed by `kQ`, `ajQ` and the projection, and lying over the generic point; $\overline{\varepsilon}$ with `hεbar`, `hεbar_aj`, a geometric point of the model lying over the cusp section and sent by $\overline{\mathrm{aj}}$ to the identity of $O$; `hpts_law`, that $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` by representability; and `hAJ`, that for any two geometric points $x$, $s$ of $\mathfrak{X}.\mathrm{Meta}.C$ with $s$ lying over the cusp there is a degree-zero divisor $D_v$ equal to $[x] - [s]$ under the bijection between geometric points and places, whose class satisfies $(O.\mathrm{pts}[D_v])_1 = x \text{ followed by } \overline{\mathrm{aj}}$.
--
--   Coefficient ring and $p$-divisible group. $R$ is a Henselian local domain which is a discrete valuation ring with algebraically closed residue field, equipped with a faithful algebra structure over which it maps into $\overline{\mathbb{Q}}$, such that: the image of $R$ lies in $Pl$ (`hRA`); $p$ is irreducible in $R$ (`hRirr`); an automorphism $\sigma$ of $\overline{\mathbb{Q}}$ lies in the inertia subgroup of $Pl$ over $\mathbb{Q}$ precisely when it fixes the image of $R$ pointwise (`hRfix`); and every element of $Pl$ fixed by that inertia subgroup lies in the image of $R$ (`hRmax`). Further, $\mathcal{G}$ is a [`PDivisibleGroup R p h`](def/PDivisibleGroup_Basic.html#L199) (a system of finite free commutative Hopf algebras `level v` over $R$ with surjective transitions, $\operatorname{rank} = p^{vh}$ and kernels the $p^v$-torsion ideals), and $\Delta$ is an injective additive map from the group $\mathcal{G}.\mathrm{Points}(\overline{\mathbb{Q}})$ to $J_H(M)$ subject to: `hΔlev`, for every $v$ the subgroup $O.\mathrm{finPts}(p^v)$ consists exactly of the images under $\Delta$ of the level-$v$ points of $\mathcal{G}$ over $\overline{\mathbb{Q}}$; `hΔgal`, $\Delta$ is equivariant for $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acting through its $R$-linear automorphisms; and `hΔhecke`, for each generator $g$ of the Hecke–diamond generator type [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) there is a compatible system of Hopf-algebra endomorphisms $\varphi_v$ of the levels commuting with the transitions, under which $\Delta$ intertwines precomposition by $\varphi_v$ with the operator `genOpH M H S g` on $J_H(M)$.
--
--   Atkin–Lehner datum. $w_{\mathrm{gen}}$ is a semilinear automorphism of $\overline{\mathbb{Q}}(X_H(M))$ over $\overline{\mathbb{Q}}$ (a pair of ring automorphisms compatible with the structure map); `hwgen` pins it on places: whenever two geometric points $y$, $y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ satisfy $y'$ followed by $\mathfrak{X}.\mathrm{eeta}$, the projection and $\mathfrak{X}.w$ equals $y$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the projection, the place of $y'$ is $w_{\mathrm{gen}}$ applied to the place of $y$. In addition $\theta$ is an $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{\mathbb{Q}}(X_H(M))$ pinned on $q$-expansions by `hθ`: whenever $f$ has the same Laurent expansion as an element $u$ of the level-$(M/p)$ field `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, the Laurent expansion of $\theta f$ is `qExpand` of that of $u$ with respect to $p$, that is $q \mapsto q^p$ on expansions; and `hwθ` asserts $w_{\mathrm{gen}} =$ `SemilinearAut.ofAlgAut θ`.
--
--   Conclusion. Under these hypotheses there exists a function
--   $$\Psi : \mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{\mathbb{Q}}(X_H(M)))[p] \longrightarrow \mathrm{qExpFunctionFieldC}\ K\ (\mathrm{CohCarrier.GammaH}\ (M / p)\ (\mathrm{ModularCurve.infSubgroup}\ p\ M\ H\ hpM))$$
--   from the $p$-torsion of the degree-zero divisor class group to the $q$-expansion function field over $K$ of level $\Gamma_{H'}(M/p)$, with $H'$ the image of $H$, such that the following five assertions hold.
--
--   First (pinning): for every $x$ in the $p$-torsion there are a degree-zero divisor $D$ on $\overline{\mathbb{Q}}(X_H(M))$, a function $f \ne 0$ in that field, and a Laurent series $y$ with coefficients in $Pl$, such that the class of $D$ equals the image of $x$ in $J_H(M)$; for every place $v$ one has $p \cdot (w_{\mathrm{gen}} \cdot D)(v) = \mathrm{ord}_v(f)$, i.e. the divisor of $f$ is $p$ times the $w_{\mathrm{gen}}$-translate of $D$; the Laurent expansion of $f$ is the coefficientwise image of $y$ under the inclusion $Pl \hookrightarrow \overline{\mathbb{Q}}$; the coefficientwise reduction of $y$ to the residue field of $Pl$ is non-zero; and the Laurent expansion of $\Psi x$ is the coefficientwise image of $y$ under $\iota_K$.
--
--   Second (multiplicativity up to constants and $p$-th powers): for all $x$, $x'$ there are $c \in K$ with $c \ne 0$ and $g$ in the target field with $\Psi(x + x') = c \cdot g^p \cdot \Psi x \cdot \Psi x'$, the constant being taken through the structure map of the target field.
--
--   Third: $\Psi x \ne 0$ for every $x$.
--
--   Fourth (orders away from the supersingular locus): for every $x$ and every place $v$ of the target field not belonging to `ssPlacesQExp K (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) p`, the integer $\mathrm{ord}_v(\Psi x)$ is divisible by $p$.
--
--   Fifth (the criterion for the finite part): for every $x$, the image of $x$ in $J_H(M)$ lies in $O.\mathrm{finPts}\,p$ — the subgroup generated by those $p$-torsion classes whose associated point of $O$ extends to a point over $\Lambda.\sigma_{Pl}$ — if and only if $p \mid \mathrm{ord}_v(\Psi x)$ for every supersingular place $v$ of the target field.
--
--   No additivity or Galois- or Hecke-equivariance is asserted of $\Psi$ itself; it is a bare function satisfying the five displayed properties.
--
--   This is the construction of a reduced $p$-th root function attached to a $p$-torsion class on $J_H(M)$ at a place above $p$ with $p$ exactly dividing $M$: the divisor of $f$ is $p$ times the Atkin–Lehner translate of a representing divisor, and the reduction of its $q$-expansion, taken in the level-$(M/p)$ function field in characteristic $p$, detects by its orders at the supersingular places whether the class belongs to the finite part of the $p$-torsion. It is used by [`ModularCurve.exists_addMonoidHom_torsion_ssPolarDifferentials_dlog_finPts_of_abelJacobiPin_tauFree_raynaud_bridgePins_export_of_algEquiv`](thm.html#ModularCurve.exists_addMonoidHom_torsion_ssPolarDifferentials_dlog_finPts_of_abelJacobiPin_tauFree_raynaud_bridgePins_export_of_algEquiv), where the logarithmic differential $d\log \Psi$ yields the Serre-style pairing between the finite part of $J_H(M)[p]$ and differentials with simple poles at the supersingular points, the local ingredient of level lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_reducedRootFunction_torsion_mem_finPts_iff_forall_dvd_ord_of_abelJacobiPin_tauFree_of_algEquiv.lean

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

theorem ModularCurve.exists_reducedRootFunction_torsion_mem_finPts_iff_forall_dvd_ord_of_abelJacobiPin_tauFree_of_algEquiv
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
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)
    :
    ∃ Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)),

      (∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y) ∧

      (∀ x x' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (c : K) (g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        Ψ (x + x') = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p * (Ψ x * Ψ x')) ∧

      (∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), Ψ x ≠ 0) ∧

      (∀ (x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) (v : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))), v ∉ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p → (p : ℤ) ∣ v.ord (Ψ x)) ∧

      (∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∈ O.finPts p ↔
        ∀ v : AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), v ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p → (p : ℤ) ∣ v.ord (Ψ x)) := by sorry
