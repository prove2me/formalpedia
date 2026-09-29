-- Prove2me | Theorems.Thm_ModularCurve_exists_section_toPic0Pair_reduction_eq_mk_and_mul_eq_ord_reducedRootFunction_of_mem_finPts_tauFree
-- name    : ModularCurve.exists_section_toPic0Pair_reduction_eq_mk_and_mul_eq_ord_reducedRootFunction_of_mem_finPts_tauFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c9aa318a-24bf-5483-baf5-6cade76e767b
-- title:
--   Reduction of a finite p-torsion class: pE is div(Ψ x)
-- statement:
--   Setting. Fix a prime $p \ne 2$ and a positive integer $M$ with $p \mid M$ and $p^{2} \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$ such that every unit which becomes $1$ in $(\mathbb{Z}/(M/p))^{\times}$ already lies in $H$ (`hHp`). A set $S \subseteq \mathbb{N}$ is carried along. The hypothesis `hin`, `HeckeDiamondInputsHAll M H`, asserts two things: for every prime $\ell$ the predicate `HeckeInputsHAlong` holds over $\overline{\mathbb{Q}}$ for $M$, $H$, $\ell$, and for every $d \in (\mathbb{Z}/M)^{\times}$ there is an $\overline{\mathbb{Q}}$-algebra automorphism $\sigma$ of the function field $F_{\overline{\mathbb{Q}}} :=$ `xHFunctionFieldBar M H` (the base change to $\overline{\mathbb{Q}}$ of the $q$-expansion function field of $X_H(M)$, realised inside $\operatorname{Laurent}(\overline{\mathbb{Q}})$) with `IsDiamondAutHBar M H d σ`. Further fixed data: a valuation subring $Pl \subseteq \overline{\mathbb{Q}}$ with $p$ a non-unit of $Pl$ (`LiesOverPrime`), whose residue field $\kappa :=$ `ResidueField ↥Pl` is algebraically closed of characteristic $p$; an algebraically closed field $K$ which is an algebra over $\mathbb{Z}/p$ and over $\kappa$; the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-one $q$-expansion function field over $\mathbb{Q}$, which is what makes the two-chart integral models available; an integral model datum $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over $R_p =$ `ratLocalizedAt p`, carrying in particular a curve model $\mathfrak{X}.\mathrm{Meta}$ over $\overline{\mathbb{Q}}$ with function field $F_{\overline{\mathbb{Q}}}$ and a comparison isomorphism $\mathfrak{X}.\mathrm{eeta}$ with the generic geometric fibre; level data $\Lambda$ and a Néron object $O :$ `JHNeronObjectAtP p M H hpM Pl hPl Λ`, whose group scheme $O.G \to$ `base p` with relative group law $O.L$ parametrises $J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}, F_{\overline{\mathbb{Q}}})$ by $O.\mathrm{pts}$ and whose special fibre is parametrised by $O.\mathrm{ptsSp}$ on the glued Picard group `GluedPic0` of the finite set of pairs of places $O.\mathrm{ssFinset}$.
--
--   Representability and Abel–Jacobi pinning (the hypotheses `hrepΛ`, `hD`, `hDQ`, `hsep`, `ajQ`, `kQ`, `ajbar`, `εbar`, `hpoinc`, `hajQε`, `hajQ`, `hkQ₁`, `hkQ₂`, `hajbar`, `hajbar_over`, `hεbar`, `hεbar_aj`, `hpts_law`, `hAJ`, summarised here). The relative Picard designations built from $\Lambda$ and from $(O.G, O.g)$ together with the $\infty$-section are assumed to represent the relative sub-Picard functor cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero of rigidified line bundles) — over $R_p$ at level $\Gamma_N$, over $R_p$ at level $\Gamma_M$, and after base change to $\mathbb{Q}$, the latter base change being separated; a section $ajQ$ of the base-changed designation and a comparison morphism $kQ$ between the two pullbacks of `toBase` are given, with $kQ$ compatible with both projections (`hkQ₁`, `hkQ₂`, the second up to $\operatorname{Spec}$ of $\mathbb{Q} \to \overline{\mathbb{Q}}$); the Poincaré bundles of the rational and integral representations correspond under base change (`hpoinc`); $ajQ$ sends the $\infty$-section to the zero section (`hajQε`) and satisfies the Abel–Jacobi characterisation `hajQ`, namely for every field $K$, every $\mathbb{Q}$-point $t$ and every $K$-point $x$ of the base-changed curve the pullback of the Poincaré bundle along $x$ followed by $ajQ$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of the $\infty$-section; $ajbar$ is the induced morphism $\mathfrak{X}.\mathrm{Meta}.C \to O.G$, defined as $\mathfrak{X}.\mathrm{eeta}$ followed by $kQ$, by $ajQ$ and by the first projection (`hajbar`), lying over the generic point (`hajbar_over`); $\bar\varepsilon$ is a geometric section of $\mathfrak{X}.\mathrm{Meta}$ reducing to the $\infty$-section (`hεbar`) and mapped by $ajbar$ to the identity of the group law (`hεbar_aj`); $O.\mathrm{pts}$ is additive for the relative group law attached to `hD` (`hpts_law`); and `hAJ` states that for all geometric points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ with $s$ pinned to the $\infty$-section there is a degree-zero divisor $D_v$ equal to $(\text{place of } x) - (\text{place of } s)$ with $(O.\mathrm{pts}\,[D_v]).1 = x.1 \circ ajbar$ (in diagrammatic order, $x.1$ followed by $ajbar$).
--
--   The inertia-fixed ring and the $p$-divisible group. $R$ is a henselian local domain which is a discrete valuation ring with algebraically closed residue field, equipped with a faithful algebra structure on $\overline{\mathbb{Q}}$ whose image lies in $Pl$ (`hRA`), in which $p$ is irreducible (`hRirr`), and which cuts out inertia: an element $\sigma \in \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ lies in `Pl.inertiaSubgroupIn ℚ` exactly when it fixes the image of $R$ pointwise (`hRfix`), and every element of $Pl$ fixed by that inertia subgroup lies in the image of $R$ (`hRmax`). For some $h$, $\mathcal{G}$ is a $p$-divisible group of height datum $h$ over $R$, and $\Delta : \mathcal{G}(\overline{\mathbb{Q}}) \to J_H(M)$ is an injective additive map (`hΔinj`) such that for each $v$ the subgroup $O.\mathrm{finPts}(p^{v})$ consists exactly of the values of $\Delta$ on level-$v$ points (`hΔlev`), $\Delta$ is equivariant for the Galois action (`hΔgal`, via automorphisms of $\overline{\mathbb{Q}}$ over $R$ agreeing with automorphisms over $\mathbb{Q}$), and every Hecke generator $g \in$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) is realised on $\mathcal{G}$ (`hΔhecke`) by a system of coalgebra endomorphisms $\varphi_v$ of the levels commuting with the transition maps and inducing `genOpH M H S g` through $\Delta$. Here $O.\mathrm{finPts}(m)$ is the subgroup generated by those $m$-torsion classes of $\mathrm{Pic}^0(\overline{\mathbb{Q}}, F_{\overline{\mathbb{Q}}})$ whose section $O.\mathrm{pts}$ satisfies `ExtendsToPlace Pl Λ.σA`.
--
--   The Atkin–Lehner datum and the reduction maps. $w_{\mathrm{gen}}$ is a semilinear automorphism of $F_{\overline{\mathbb{Q}}}$ over $\overline{\mathbb{Q}}$, that is, a pair of ring automorphisms of $F_{\overline{\mathbb{Q}}}$ and of $\overline{\mathbb{Q}}$ compatible with the structure map, and `hwgen` states that it induces on places the effect of $\mathfrak{X}.w$ on geometric points. The ring homomorphism $\iota_K : Pl \to K$ has as kernel the maximal ideal (`hιK`: $\iota_K y = 0$ iff the valuation of $y$ is $< 1$) and factors as the residue map followed by $\kappa \to K$ (`hιKres`). A homomorphism $\rho : R_p \to Pl$ is compatible with the structure map to $\overline{\mathbb{Q}}$ (`hρ`) and induces $\Lambda.\sigma_A$ (`hσA`). The hypothesis `hsp` (a specialisation statement for Abel–Jacobi, whose many clauses are summarised here) asserts: for each $i \in \{0,1\}$, given two geometric points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$, lifts $u_1, u_2$ over $\operatorname{Spec} \rho$ whose images lie in the smooth locus and which are compatible with the given geometric points, residual points $u_{\kappa,1}, u_{\kappa,2}$ of the fibre over $\kappa$ compatible with the $u_j$ and sections of the fibre structure, closed points $P_1, P_2$ of the fibre curve $\mathfrak{X}.\mathrm{Mfib}$ lying over the closed points of $u_{\kappa,1}, u_{\kappa,2}$, a degree-zero divisor $D_v$ equal to the difference of the places of $y_1$ and $y_2$, and an admissible gluing datum $x$ for $O.\mathrm{ssFinset}$ whose first divisor component is the difference of the places of $P_1, P_2$ if $i = 0$ and $0$ otherwise, whose second divisor component is that same difference if $i = 1$ and $0$ otherwise, and whose unit component vanishes — then there is a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $(O.\mathrm{pts}\,[D_v]).1 =$ `barPt Pl` followed by $s.1$ and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along `resPt Pl` equal to the class of $x$ in `GluedPic0`.
--
--   The special-fibre function field and the reduced root function. $\bar F_\kappa :=$ `JHNeronObjectAtP.Fbar p M H hpM κ` is the level-$\Gamma_N(p,M,H)$ $q$-expansion function field over $\kappa$. A ring homomorphism $e_K : \bar F_\kappa \to$ `qExpFunctionFieldC K (GammaH (M/p) (infSubgroup p M H hpM))` is given which on Laurent series is coefficientwise application of $\kappa \to K$ (`heK`), together with a map $pl_K$ on places such that $\operatorname{ord}_{pl_K(v)}(e_K g) = \operatorname{ord}_v(g)$ for all $g$ and $v$ (`hplK`). Finally $\Psi$ assigns to every $p$-torsion class $x$ of $\mathrm{Pic}^0(\overline{\mathbb{Q}}, F_{\overline{\mathbb{Q}}})$ an element of `qExpFunctionFieldC K (GammaH (M/p) (infSubgroup p M H hpM))` subject to `hΨ`: there are a degree-zero divisor $D$ with class $x$, a non-zero $f \in F_{\overline{\mathbb{Q}}}$ with $p \cdot (w_{\mathrm{gen}} \cdot D)(v) = \operatorname{ord}_v(f)$ for every place $v$, and a Laurent series $y$ over $Pl$ with $f =$ `coeffMap Pl.subtype y`, with `coeffMap (residue) y` $\ne 0$, and with $\Psi x =$ `coeffMap ιK y` as Laurent series over $K$. An additive map $W :=$ `Wbar` on $J_H(M)$ is given with $W x = w_{\mathrm{gen}} \cdot x$ for all $x$ (`hWbar`).
--
--   Conclusion. For every $p$-torsion class $x \in \mathrm{Pic}^0(\overline{\mathbb{Q}}, F_{\overline{\mathbb{Q}}})[p]$ whose underlying class in $J_H(M)$ lies in $O.\mathrm{finPts}(p)$, there exist a section $s$ of $O.g$ over $\Lambda.\sigma_A$ and a degree-zero divisor $E$ on $\bar F_\kappa$ over $\kappa$ such that:
--
--   (i) the section of $O.g$ over the generic geometric point attached to $W x$ is the restriction of $s$, that is $(O.\mathrm{pts}(W x)).1 =$ `barPt Pl` followed by $s.1$;
--
--   (ii) the class of $E$ in $\mathrm{Pic}^0(\kappa, \bar F_\kappa)$ equals the first component of `GluedPic0.toPic0Pair O.ssFinset` applied to $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along `resPt Pl`, i.e. the class of the first divisor component of the gluing datum describing the reduction of $s$;
--
--   (iii) for every place $v$ of $\bar F_\kappa$ over $\kappa$ one has $p \cdot E(v) = \operatorname{ord}_{pl_K(v)}(\Psi x)$.
--
--   Thus (iii) records the divisor identity $p E = \operatorname{div}(\Psi x)$ read off place by place through $pl_K$, rather than as an equality of principal divisors.
--
--   This is the Serre-compatibility step for the reduced $p$-th-root function: on the finite part of $J_H(M)[p]$ at a place above $p$ (with $p \Vert M$), the function $\Psi$ constructed on the special fibre is a $p$-th-root function for the Atkin–Lehner translate of the class, its divisor being $p$ times the $\Sigma^\infty$-coordinate of the reduction of the corresponding Néron section. It is used in the analysis of the $p$-torsion of the special fibre at level $\Gamma_H(M)$ — via Serre's $\mathrm{dlog}$ and the Cartier-fixed differentials — which feeds the level-lowering at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_section_toPic0Pair_reduction_eq_mk_and_mul_eq_ord_reducedRootFunction_of_mem_finPts_tauFree.lean

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
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

set_option maxHeartbeats 800000 in
open ModularCurve in

theorem ModularCurve.exists_section_toPic0Pair_reduction_eq_mk_and_mul_eq_ord_reducedRootFunction_of_mem_finPts_tauFree
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

    (ιK : ↥Pl →+* K) (hιK : ∀ y : ↥Pl, ιK y = 0 ↔ Pl.valuation (y : AlgebraicClosure ℚ) < 1)

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    [Algebra (IsLocalRing.ResidueField ↥Pl) K]
    (hιKres : ∀ y : ↥Pl, ιK y = algebraMap (IsLocalRing.ResidueField ↥Pl) K (IsLocalRing.residue ↥Pl y))
    (eK : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl) →+* ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (heK : ∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl), ((eK g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap (IsLocalRing.ResidueField ↥Pl) K) (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)))
    (plK : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) → AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))))
    (hplK : ∀ (g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)) (v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))), (plK v).ord (eK g) = v.ord g)

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)

    (Wbar : ModularCurve.JH M H →+ ModularCurve.JH M H)
    (hWbar : ∀ x : ModularCurve.JH M H, Wbar x = wgen • x)
    :

    ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∈ O.finPts p →
      ∃ (s : NeronModelInfra.SchemeHomOver Λ.σA O.g)
        (E : AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))),
        (O.pts (Wbar ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H))).1 = ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ s.1 ∧
        AlgebraicCurve.Pic0.mk E =
          (AlgebraicCurve.GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨ModularCurve.JZeroNeronObjectAtP.resPt Pl, rfl⟩ s))).1 ∧
        ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          (p : ℤ) * (E : AlgebraicCurve.Divisor (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))) v = (plK v).ord (Ψ x) := by sorry
