-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_wbar_mem_finPts_of_mem_finPts_of_abelJacobiPin_tauFree
-- name    : ModularCurve.JHNeronObjectAtP.wbar_mem_finPts_of_mem_finPts_of_abelJacobiPin_tauFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/03583735-f689-57c5-b869-086ddd1d8a12
-- title:
--   Stability of the finite part under the Atkin–Lehner translate
-- statement:
--   The setting is a prime $p \neq 2$ and a level $M$ with $p \mid M$ but $p^2 \nmid M$, together with a subgroup $H \le (\mathbf{Z}/M)^\times$ satisfying `hHp`: every unit $u$ of $\mathbf{Z}/M$ whose image under the reduction map $(\mathbf{Z}/M)^\times \to (\mathbf{Z}/(M/p))^\times$ is trivial lies in $H$. A set of primes $S$ is given, and `hin : HeckeDiamondInputsHAll M H` packages the Hecke and diamond inputs at level $(M,H)$: for every prime $\ell$ the predicate `HeckeInputsHAlong` over $\overline{\mathbf{Q}}$ at $\ell$ holds, and for every $d \in (\mathbf{Z}/M)^\times$ there is an $\overline{\mathbf{Q}}$-automorphism of the function field $\overline{\mathbf{Q}} \cdot X_H(M)$ realising the diamond operator $\langle d \rangle$.
--
--   A valuation subring $Pl$ of $\overline{\mathbf{Q}}$ is fixed with `hPl : Pl.LiesOverPrime p`, i.e. $p$ is a non-unit of $Pl$; its residue field is of characteristic $p$ and algebraically closed. The hypothesis `hj` asserts that the $q$-expansion `jqModC ℚ` of $j$ lies in the field `qExpFunctionFieldC ℚ ⊤`, which makes the two-chart integral model over $R_p = \mathbf{Z}_{(p)}$ available; $\mathfrak{X}$ is an `XHDRModelAtP p M H hpM hj`, the Deligne–Rapoport-style model datum for $X_H(M)$ over $R_p$ together with its curve model `𝔛.Meta` over $\overline{\mathbf{Q}}$ with function field $\overline{\mathbf{Q}} \cdot X_H(M)$.
--
--   Néron data. $\Lambda$ is a `JHNeronObjectAtP.LevelData p M H hpM Pl`: a section $\sigma_A$ of the base $\operatorname{Spec} R_p$ over $Pl$ restricting to the geometric generic point, a scheme $X \to \operatorname{Spec} R_p$ with a relative group law and identifications of $J_H(M/p)$-points and of $\operatorname{Pic}^0$ of the reduction with sections. The hypothesis `hrepΛ` asserts that the relative $\operatorname{Pic}^0$ designation built from $\Lambda.X$, $\Lambda.f$ and the identity of $\Lambda.L$ represents the fibrewise-algebraically-equivalent-to-zero subfunctor of the relative Picard functor of the level-$\Gamma_N$ model, with the rigidifying section obtained from $\mathfrak{X}.\varepsilon_{\inf}$ and $\mathfrak{X}.\pi$. $O$ is a `JHNeronObjectAtP p M H hpM Pl hPl Λ`: a smooth, separated, surjective, quasi-compact group scheme $g : G \to \operatorname{Spec} R_p$ of locally finite type with connected fibres, a relative commutative group law $O.L$, a bijection $O.\mathrm{pts} : J_H(M) \to$ sections of $g$ over the geometric generic point which is additive and Galois-equivariant, Hecke correspondences compatible with $O.\mathrm{pts}$, flatness and surjectivity of multiplication by $n$, properness of the generic fibre, and the further clauses of that structure.
--
--   Representability and Abel–Jacobi pinning. The hypotheses `hD` and `hDQ` assert that $(O.G, O.g)$ with the identity rigidification represents the fibrewise-algebraically-trivial subfunctor of the relative Picard functor of the $R_p$-model, respectively of its base change to $\mathbf{Q}$ with the base-changed section; `hsep` asserts that the generic fibre is separated. Then $ajQ$ is a section over the $\mathbf{Q}$-fibre of the base-changed designation, $kQ$ a morphism from the $\overline{\mathbf{Q}}$-fibre to the $\mathbf{Q}$-fibre of the model, $\overline{aj} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$, and $\bar\varepsilon$ an $\overline{\mathbf{Q}}$-point of `𝔛.Meta.C` over the base. The compatibilities are: `hpoinc`, the Poincaré bundle of `hDQ` is isomorphic to the base change to $\mathbf{Q}$ of the pullback of the Poincaré bundle of `hD` along the first projection; `hajQε`, composing the base-changed zero section with $ajQ$ gives the zero section of the base-changed designation; `hajQ`, for every field $K$, every $K$-point $t$ of $\operatorname{Spec}\mathbf{Q}$ and every $x$ over $t$ in the generic fibre, the pullback of the Poincaré bundle along $x$ followed by $ajQ$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor cut out by the zero section at $t$, i.e. $ajQ$ is the Abel–Jacobi map $x \mapsto [x - \varepsilon]$; `hkQ₁`, `hkQ₂`, which say that $kQ$ is the canonical comparison of the two fibres over $\operatorname{Spec}\mathbf{Q}$ and $\operatorname{Spec}\overline{\mathbf{Q}}$; `hajbar`, $\overline{aj}$ is $\mathfrak{X}.\mathrm{eeta}$ followed by $kQ$, $ajQ$ and the first projection; `hajbar_over`, $\overline{aj}$ lies over the geometric generic point; `hεbar` and `hεbar_aj`, the point $\bar\varepsilon$ maps to the cusp section $\mathfrak{X}.\varepsilon_{\inf}$ and $\overline{aj} \circ \bar\varepsilon$ is the identity section of $O.L$; `hpts_law`, $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` through the representability; and `hAJ`, for all $\overline{\mathbf{Q}}$-points $x, s$ of `𝔛.Meta.C` with $s$ lying over $\mathfrak{X}.\varepsilon_{\inf}$, there is a degree-zero divisor $Dv$ equal to $(\text{place of } x) - (\text{place of } s)$ whose class satisfies $O.\mathrm{pts}([Dv]) = x$ followed by $\overline{aj}$.
--
--   A local ring $R$ is given: a Henselian local domain with algebraically closed residue field, an algebra over which $\overline{\mathbf{Q}}$ is faithful, with `hRA` its image contained in $Pl$, `hRdvr` that $R$ is a discrete valuation ring, `hRirr` that $p$ is irreducible in $R$, `hRfix` that the inertia subgroup of $Pl$ over $\mathbf{Q}$ consists exactly of those $\sigma$ fixing the image of $R$ pointwise, and `hRmax` that every element of $Pl$ fixed by that inertia subgroup comes from $R$.
--
--   $p$-divisible group data. $\mathcal{G}$ is a [`PDivisibleGroup R p h`](def/PDivisibleGroup_Basic.html#L199) (a system of finite free cocommutative Hopf algebras `level v` over $R$ of rank $p^{vh}$ with surjective transitions whose kernels are the $p^v$-torsion ideals), and $\Delta$ is an additive map from its $\overline{\mathbf{Q}}$-points to $J_H(M)$, with: `hΔinj`, injectivity; `hΔlev`, for every $v$ a point $y$ lies in $O.\mathrm{finPts}(p^v)$ if and only if $y = \Delta$ of a point of level $v$; `hΔgal`, $\Delta$ is equivariant for $\sigma \in \operatorname{Gal}(\overline{\mathbf{Q}}/\mathbf{Q})$ whenever an $R$-algebra automorphism induces the same map on $\overline{\mathbf{Q}}$; and `hΔhecke`, for every set of primes $S$ and every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) there is a compatible system of coalgebra endomorphisms $\varphi_v$ of the levels commuting with the transitions and inducing, through $\Delta$, the Hecke or diamond operator `genOpH M H S g` on $J_H(M)$.
--
--   The Atkin–Lehner datum is a semilinear automorphism $w_{\mathrm{gen}}$ of the function field $\overline{\mathbf{Q}} \cdot X_H(M)$ over $\overline{\mathbf{Q}}$ (a pair consisting of a ring automorphism of the field and one of $\overline{\mathbf{Q}}$, compatible with the structure map), with `hwgen`: whenever two $\overline{\mathbf{Q}}$-points $y, y'$ of `𝔛.Meta.C` satisfy that $y'$ followed by the model embedding and $\mathfrak{X}.w$ equals $y$ followed by the model embedding, the place attached to $y'$ is $w_{\mathrm{gen}}$ acting on the place attached to $y$. Furthermore $\rho : R_p \to Pl$ is a ring homomorphism with `hρ` stating that it is the structure map $R_p \to \overline{\mathbf{Q}}$ after inclusion, and `hσA` identifies $\Lambda.\sigma_A$ with $\operatorname{Spec}$ of $\rho$.
--
--   The hypothesis `hsp` (a specialisation statement, its twenty-one arguments summarised here) asserts the following: for each $i \in \{0,1\}$, each pair of $\overline{\mathbf{Q}}$-points $y_1, y_2$ of `𝔛.Meta.C` together with $Pl$-points $u_1, u_2$ of the model whose restriction to $\overline{\mathbf{Q}}$ agrees with $y_1, y_2$ and whose images lie in the smooth locus $\mathfrak{X}.\mathrm{smoothLocus}$, each lift $u_{\kappa 1}, u_{\kappa 2}$ of these to the special fibre over the residue field of $Pl$, and each pair of closed points $P_1, P_2$ of the curve model `(𝔛.Mfib Pl hPl ρ hρ).C` of the special fibre lying over the images of the closed point under $u_{\kappa 1}, u_{\kappa 2}$, given a degree-zero divisor $Dv$ on the generic curve equal to $(\text{place of } y_1) - (\text{place of } y_2)$ and an admissible gluing datum $x$ for the finite set $O.\mathrm{ssFinset}$ of pairs of places whose first component is $(\text{place of } P_1) - (\text{place of } P_2)$ if $i = 0$ and $0$ otherwise, whose second component is the same difference if $i = 1$ and $0$ otherwise, and whose unit component vanishes, there exists a section $s$ of $O.g$ over $\Lambda.\sigma_A$ such that $O.\mathrm{pts}([Dv])$ is the restriction of $s$ to $\overline{\mathbf{Q}}$ and the image of the restriction of $s$ to the residue field under $O.\mathrm{ptsSp}^{-1}$ is the class of $x$ in the glued $\operatorname{Pic}^0$ of $O.\mathrm{ssFinset}$.
--
--   Finally $\overline{W} : J_H(M) \to J_H(M)$ is an additive endomorphism with `hWbar : ∀ x, Wbar x = wgen • x`, i.e. $\overline{W}$ is the action of the semilinear automorphism $w_{\mathrm{gen}}$ on divisor classes.
--
--   Conclusion: for every $m \in \mathbf{N}$ and every $x \in J_H(M)$, if $x$ lies in $O.\mathrm{finPts}\, m$ — the subgroup of $J_H(M)$ generated by those classes that are $m$-torsion in $\operatorname{Pic}^0(\overline{\mathbf{Q}} \cdot X_H(M))$ and whose associated $\overline{\mathbf{Q}}$-section $O.\mathrm{pts}(x)$ extends to a section over $Pl$ along $\Lambda.\sigma_A$ — then $\overline{W} x$ again lies in $O.\mathrm{finPts}\, m$.
--
--   The subgroup $O.\mathrm{finPts}\, m$ is the finite part of the $m$-torsion of $J_H(M)$ at the chosen place above $p$, read off from a Néron-type model $G \to \operatorname{Spec}\mathbf{Z}_{(p)}$ pinned to the Abel–Jacobi map of the Deligne–Rapoport model; the statement records that this subgroup is stable under the Atkin–Lehner translate $\overline{W}$, which acts on divisor classes through the semilinear automorphism $w_{\mathrm{gen}}$ of the function field matched with the model automorphism $\mathfrak{X}.w$. It is used in the level-lowering analysis at a prime exactly dividing the level, feeding the divisibility statement for orders of reduced root functions and the construction of configured representatives of classes in the finite part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_wbar_mem_finPts_of_mem_finPts_of_abelJacobiPin_tauFree.lean

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

theorem ModularCurve.JHNeronObjectAtP.wbar_mem_finPts_of_mem_finPts_of_abelJacobiPin_tauFree
    (p : ℕ)
    [Fact p.Prime]
    (hp2 : p ≠ 2)
    (M : ℕ)
    [NeZero M]
    (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ))
    (hPl : Pl.LiesOverPrime p)

    [CharP (IsLocalRing.ResidueField ↥Pl) p]
    [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π) (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
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

    (R : Type)
    [CommRing R]
    [IsDomain R]
    [HenselianLocalRing R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]

    [Algebra R (AlgebraicClosure ℚ)]
    [FaithfulSMul R (AlgebraicClosure ℚ)]
    (hRA : ∀ x : R, algebraMap R (AlgebraicClosure ℚ) x ∈ Pl)
    (hRdvr : IsDiscreteValuationRing R)
    (hRirr : Irreducible ((p : ℕ) : R))
    (hRfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ ∈ Pl.inertiaSubgroupIn ℚ ↔ ∀ x : R, σ (algebraMap R (AlgebraicClosure ℚ) x) = algebraMap R (AlgebraicClosure ℚ) x)
    (hRmax : ∀ y ∈ Pl, (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, σ y = y) → ∃ x : R, algebraMap R (AlgebraicClosure ℚ) x = y)

    {h : ℕ}
    (𝒢 : PDivisibleGroup R p h)
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

    (ρ : ModularCurve.XHDRLevel.R p →+* ↥Pl)
    (hρ : Pl.subtype.comp ρ = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
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

    (Wbar : ModularCurve.JH M H →+ ModularCurve.JH M H)
    (hWbar : ∀ x : ModularCurve.JH M H, Wbar x = wgen • x)
    :
    ∀ (m : ℕ) (x : ModularCurve.JH M H), x ∈ O.finPts m → Wbar x ∈ O.finPts m := by sorry
