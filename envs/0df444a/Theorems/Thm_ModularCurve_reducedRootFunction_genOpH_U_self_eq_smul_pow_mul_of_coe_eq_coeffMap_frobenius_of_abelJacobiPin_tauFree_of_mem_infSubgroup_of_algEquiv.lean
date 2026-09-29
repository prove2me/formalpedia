-- Prove2me | Theorems.Thm_ModularCurve_reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv
-- name    : ModularCurve.reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/8ca5a072-e1a2-55ff-8baa-48c211208473
-- title:
--   Frobenius twist of the reduced root function under Uₚ
-- statement:
--   Fix a prime $p \neq 2$ and an integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbf{Z}/M)^\times$ and a set $S \subseteq \mathbf{N}$. The hypothesis `hHp` requires that every unit $u$ of $\mathbf{Z}/M$ whose image in $(\mathbf{Z}/(M/p))^\times$ is trivial already lies in $H$, and `hin` is the conjunction `HeckeDiamondInputsHAll M H`: for every prime $\ell$ the predicate `HeckeInputsHAlong` holds over $\overline{\mathbf{Q}}$ at level $(M,H)$ and $\ell$, and for every $d \in (\mathbf{Z}/M)^\times$ there is an $\overline{\mathbf{Q}}$-algebra automorphism $\sigma$ of the function field $\overline{\mathbf{Q}}F_H(M) =$ `xHFunctionFieldBar M H` satisfying the predicate `IsDiamondAutHBar M H d`. Further data: a valuation subring $Pl$ of $\overline{\mathbf{Q}}$ with $p$ in its nonunits, whose residue field is algebraically closed of characteristic $p$; an algebraically closed field $K$ of characteristic $p$; and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the Laurent-series subfield `qExpFunctionFieldC ℚ ⊤` of the full modular group.
--
--   The geometric frame consists of: a Deligne–Rapoport type integral model $\mathfrak{X} =$ `XHDRModelAtP p M H hpM hj` at $p$, which in particular provides a curve model $\mathfrak{X}.\mathrm{Meta}$ of $\overline{\mathbf{Q}}F_H(M)$ over $\overline{\mathbf{Q}}$, an isomorphism $\mathfrak{X}.\mathtt{eeta}$ of its underlying curve with the $\overline{\mathbf{Q}}$-fibre of the $\Gamma_M$-model, a section `𝔛.εinf` of the $\Gamma_M$-model over the base ring `R p`, a morphism `𝔛.π` of the $\Gamma_M$-model to the $\Gamma_N$-model over that base, and an isomorphism `𝔛.w`; level data $\Lambda$ for the $\Gamma_N$-level Néron object, together with `hrepΛ`, the (nonempty) assertion that the designation $(\Lambda.X,\Lambda.f,\text{unit section})$ represents the relative sub-Picard functor cut out by fibrewise algebraic equivalence to zero for the $\Gamma_N$-model with section `schemeHomOverComp 𝔛.εinf 𝔛.π`; a Néron object $O$ for $J_H(M)$ over the base, whose points are indexed by $J_H(M)$ and which carries a relative group law and Hecke correspondences; the representability hypotheses `hD` and `hDQ` for the designation built from $(O.G,O.g)$, over the base and after base change to $\mathbf{Q}$ respectively; separatedness `hsep` of the generic fibre; an Abel–Jacobi morphism `ajQ` over $\mathbf{Q}$ from the base-changed curve to the base of the base-changed designation; a comparison morphism `kQ` between the $\overline{\mathbf{Q}}$- and $\mathbf{Q}$-pullbacks of the $\Gamma_M$-model; a morphism `ajbar` from $\mathfrak{X}.\mathrm{Meta}.C$ to $O.G$; and a $\overline{\mathbf{Q}}$-point `εbar` of $\mathfrak{X}.\mathrm{Meta}.C$ over the base. These are pinned by the following hypotheses, each of which is used as stated: `hpoinc`, that the Poincaré bundle of `hDQ` is isomorphic to the base change to $\mathbf{Q}$ of the Poincaré bundle of `hD` pulled back along the first projection of $O.g$; `hajQε`, that the zero section of the base-changed curve followed by `ajQ` is the zero section of the base-changed designation; `hajQ`, that for every field, every morphism $t$ of its spectrum to $\operatorname{Spec}\mathbf{Q}$ and every $t$-point $x$ of the base-changed curve, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by `ajQ` is isomorphic to the tensor product of the line bundle (dual ideal module) of the relative effective Cartier divisor of the point $x$ with the ideal module of the relative effective Cartier divisor of the point $t$ followed by the base-changed cusp section; `hkQ₁` and `hkQ₂`, identifying the two projections of `kQ` with the projections of the $\overline{\mathbf{Q}}$-pullback, the second up to $\operatorname{Spec}\overline{\mathbf{Q}} \to \operatorname{Spec}\mathbf{Q}$; `hajbar`, that `ajbar` is $\mathfrak{X}.\mathtt{eeta}$ followed by `kQ`, by `ajQ` and by the first projection of $O.g$; `hajbar_over`, that `ajbar` followed by $O.g$ is $\mathfrak{X}.\mathrm{Meta}.\mathrm{toBase}$ followed by the generic point of the base; `hεbar`, that `εbar` followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection is the generic point followed by `𝔛.εinf`; `hεbar_aj`, that `εbar` followed by `ajbar` is the generic point followed by the unit of the group law of $O$; `hpts_law`, that $O.\mathrm{pts}$ is additive for the relative group law attached to `hD` via the algebraic-equivalence-to-zero group cut; and `hAJ`, that for all $\overline{\mathbf{Q}}$-points $x,s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base with $s$ satisfying the cusp condition of `hεbar`, there is a degree-zero divisor $D_v$ on $\overline{\mathbf{Q}}F_H(M)$ equal to the difference of the places of $x$ and of $s$ (each with multiplicity one, under the bijection `pointEquivPlace`) with $O.\mathrm{pts}(\mathrm{Pic}^0\,D_v)$ given by $x$ followed by `ajbar`.
--
--   Next, a commutative domain $R$ which is a Henselian local ring with algebraically closed residue field, an $R$-algebra structure on $\overline{\mathbf{Q}}$ with faithful scalar action, such that: `hRA`, the image of $R$ in $\overline{\mathbf{Q}}$ lies in $Pl$; `hRdvr`, $R$ is a discrete valuation ring; `hRirr`, $p$ is irreducible in $R$; `hRfix`, an automorphism $\sigma$ of $\overline{\mathbf{Q}}$ over $\mathbf{Q}$ lies in the inertia subgroup of $Pl$ over $\mathbf{Q}$ (the image of the inertia subgroup inside the decomposition subgroup) if and only if it fixes the image of $R$ pointwise; and `hRmax`, every element of $Pl$ fixed by that inertia subgroup lies in the image of $R$.
--
--   Next, a natural number $h$ and a $p$-divisible group $\mathcal{G}$ over $R$ of height $h$ (finite free cocommutative Hopf algebras `𝒢.level v` with surjective transitions, $\operatorname{rank} = p^{vh}$, and kernel of the $v$-th transition the $p^v$-torsion ideal), together with an additive map $\Delta$ from the $\overline{\mathbf{Q}}$-points of $\mathcal{G}$ (the direct limit of the level-$v$ point groups) to $J_H(M) = \mathrm{Pic}^0(\overline{\mathbf{Q}}, \overline{\mathbf{Q}}F_H(M))$, subject to: `hΔinj`, injectivity of $\Delta$; `hΔlev`, for every $v$ and every $y \in J_H(M)$, that $y$ lies in $O.\mathrm{finPts}(p^v)$ — the subgroup generated by the $p^v$-torsion classes whose associated point extends to a section over $Pl$ — if and only if $y = \Delta$ of the image of some level-$v$ point; `hΔgal`, that for $\tau$ an automorphism of $\overline{\mathbf{Q}}$ over $\mathbf{Q}$ and $\tau'$ an $R$-algebra automorphism of $\overline{\mathbf{Q}}$ with the same underlying map, $\Delta(\tau' \cdot z) = \tau \cdot \Delta(z)$; and `hΔhecke`, that for every set $S$ of naturals and every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a $T_\ell$, a $U_q$ or a diamond $\langle d\rangle$) there is a family of $R$-coalgebra-algebra endomorphisms $\varphi_v$ of `𝒢.level v` commuting with the transition maps, such that $\Delta$ carries precomposition of level-$v$ points by $\varphi_v$ to the action of `genOpH M H S g` on $J_H(M)$.
--
--   Next, a semilinear automorphism $w_{\mathrm{gen}}$ of $\overline{\mathbf{Q}}F_H(M)$ over $\overline{\mathbf{Q}}$, i.e. a pair consisting of a ring automorphism of the function field and a ring automorphism of $\overline{\mathbf{Q}}$ compatible with the structure map, with `hwgen`: whenever two $\overline{\mathbf{Q}}$-points $y,y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base satisfy that $y'$ followed by $\mathfrak{X}.\mathtt{eeta}$, the first projection and `𝔛.w.hom` equals $y$ followed by $\mathfrak{X}.\mathtt{eeta}$ and the first projection, the place of $y'$ is $w_{\mathrm{gen}}$ applied to the place of $y$. It is pinned on $q$-expansions by an $\overline{\mathbf{Q}}$-algebra automorphism $\theta$ of $\overline{\mathbf{Q}}F_H(M)$ with `hθ`: for $f$ in $\overline{\mathbf{Q}}F_H(M)$ and $u$ in $\overline{\mathbf{Q}}F_{H^{\infty}}(M/p)$, where $H^{\infty} =$ `infSubgroup p M H hpM` is the image of $H$ in $(\mathbf{Z}/(M/p))^\times$, having the same Laurent series, the Laurent series of $\theta f$ is `qExpand` at $p$ of that of $u$ (substitution $q \mapsto q^p$ on exponents); and `hwθ`: $w_{\mathrm{gen}}$ is the image of $\theta$ under `SemilinearAut.ofAlgAut`.
--
--   Finally, a ring homomorphism $\iota_K : Pl \to K$ with `hιK`: $\iota_K y = 0$ exactly when the valuation of $y$ is $< 1$, so that $\iota_K$ kills precisely the maximal ideal; and a map
--   $$\Psi : \mathrm{Pic}^0(\overline{\mathbf{Q}}, \overline{\mathbf{Q}}F_H(M))[p] \longrightarrow \mathtt{qExpFunctionFieldC}\,K\,(\Gamma_{H^{\infty}}(M/p))$$
--   subject to `hΨ`: for every $p$-torsion class $x$ there exist a degree-zero divisor $D$ on $\overline{\mathbf{Q}}F_H(M)$, a nonzero element $f$ of that function field and a Laurent series $y$ with coefficients in $Pl$ such that the class of $D$ in $J_H(M)$ is $x$; $f \neq 0$; for every place $v$ one has $p \cdot (w_{\mathrm{gen}} \cdot D)(v) = \operatorname{ord}_v f$; the Laurent series of $f$ is the coefficientwise image of $y$ under $Pl \hookrightarrow \overline{\mathbf{Q}}$; the coefficientwise reduction of $y$ to the residue field of $Pl$ is nonzero; and the Laurent series of $\Psi x$ is the coefficientwise image of $y$ under $\iota_K$. A unit $d$ of $\mathbf{Z}/M$ is given whose image in $\mathbf{Z}/(M/p)$ equals $p$ (`hd`), and `hdH` requires that the image of $d$ in $(\mathbf{Z}/(M/p))^\times$ or its negative lies in $H^{\infty}$.
--
--   Under these hypotheses the conclusion is: for all $p$-torsion classes $x$ and $y$ in $\mathrm{Pic}^0(\overline{\mathbf{Q}}, \overline{\mathbf{Q}}F_H(M))$ such that the image of $y$ in $J_H(M)$ equals `genOpH M H S (CohCarrier.Gen.U p _ hpM)` — the Hecke operator $U_p$ at level $(M,H)$ — applied to the image of $x$, there exist $c \in K$ and elements $g, f'$ of $\mathtt{qExpFunctionFieldC}\,K\,(\Gamma_{H^{\infty}}(M/p))$ such that: $c \neq 0$; the Laurent series of $f'$ is the image of the Laurent series of $\Psi x$ under the coefficientwise $p$-power Frobenius of $K$; and $\Psi y = \iota(c) \cdot g^p \cdot f'$, where $\iota$ denotes the structure map of $K$ into that function field.
--
--   This is the $U_p$-law for the reduced root function attached to the $p$-torsion of $J_H(M)$ in the Deligne–Rapoport integral model at $p$: the $q$-expansion of the root function of $U_p x$ differs from the coefficientwise Frobenius twist of that of $x$ only by a constant and a $p$-th power. It is used in the construction of the $\mathrm{dlog}$ map from the $p$-divisible group's points into polar differentials on the special fibre, the analytic input to the level-lowering argument at a prime exactly dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv.lean

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

theorem ModularCurve.reducedRootFunction_genOpH_U_self_eq_smul_pow_mul_of_coe_eq_coeffMap_frobenius_of_abelJacobiPin_tauFree_of_mem_infSubgroup_of_algEquiv
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

    [CharP K p]

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    :
    ∀ (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
      ((y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) = ModularCurve.genOpH M H S (CohCarrier.Gen.U p Fact.out hpM) ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) →
      ∃ (c : K) (g f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), c ≠ 0 ∧
        ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap (frobenius K p) ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) ∧
        Ψ y = algebraMap K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) c * g ^ p * f' := by sorry
