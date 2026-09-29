-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_section_toPic0Pair_eq_mk_of_mem_finPts_of_forall_dvd_ord_tauFree
-- name    : ModularCurve.JHNeronObjectAtP.exists_section_toPic0Pair_eq_mk_of_mem_finPts_of_forall_dvd_ord_tauFree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/c0a3248d-7100-5bdf-95c9-e85e36f26a3e
-- title:
--   Reduced Néron section of a finite p-torsion class
-- statement:
--   Fix a prime $p \neq 2$ and a modulus $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a set $S \subseteq \mathbb{N}$. The hypothesis `hHp` requires every unit of $(\mathbb{Z}/M)^{\times}$ whose image under `ZMod.unitsMap` for $M/p \mid M$ is trivial to lie in $H$, and `hin` is `HeckeDiamondInputsHAll M H`, i.e. the conjunction of the Hecke input conditions at every prime $\ell$ for the level-$(M,H)$ function field over $\overline{\mathbb{Q}}$ together with the existence, for each $d \in (\mathbb{Z}/M)^{\times}$, of a diamond automorphism realising $d$.
--
--   Let $\mathfrak{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ (that is, $p$ is a non-unit of $\mathfrak{Pl}$), with residue field of characteristic $p$ and algebraically closed, and let `hj` assert that the $q$-expansion `jqModC ℚ` of $j$ lies in the $q$-expansion function field of level $\mathrm{SL}(2,\mathbb{Z})$ over $\mathbb{Q}$. Let $\mathfrak{X}$ be a model `XHDRModelAtP p M H hpM hj` of the modular curve at $p$ (carrying, among other data, the proper flat integral model of level $\Gamma_M$, the smooth proper model of level $\Gamma_N$, the curve model `𝔛.Meta` of the function field $\overline{F}_H =$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ together with the isomorphism `𝔛.eeta` onto the generic geometric fibre, the involution `𝔛.w`, the sections `𝔛.εinf`, `𝔛.π`, and the special-fibre data `𝔛.Mfib`, `𝔛.efib`, `𝔛.comp`). Let $\Lambda$ be level data `JHNeronObjectAtP.LevelData p M H hpM Pl` (a structure morphism $\Lambda.\sigma_A$ to the base over $\mathfrak{Pl}$ compatible with the geometric generic point, a scheme $\Lambda.X$ over the base with relative group law $\Lambda.L$, and bijections of the points of $J$ at level $M/p$, respectively of the glued Picard group over the residue field, with the corresponding sections), and let `hrepΛ` assert that the relative $\mathrm{Pic}^0$ designation $(\Lambda.X, \Lambda.f, \text{unit section of } \Lambda.L)$ represents the subfunctor of the relative Picard functor of the level-$\Gamma_N$ model, rigidified along `𝔛.εinf` followed by `𝔛.π`, cut out by fibrewise algebraic equivalence to zero. Let $O$ be a Néron object `JHNeronObjectAtP p M H hpM Pl hPl Λ` for $J_H(M)$.
--
--   The representability and Abel–Jacobi frame consists of: `hD`, that the designation $(O.G, O.g, \text{unit section of } O.L)$ represents the same fibrewise-algebraically-trivial subfunctor for the level-$\Gamma_M$ model rigidified along `𝔛.εinf`; `hDQ`, the corresponding statement for the base change of that designation to $\mathbb{Q}$, rigidified along `sectionBaseChange ℚ 𝔛.εinf`; `hsep`, separatedness of the generic fibre of the level-$\Gamma_M$ model over $\mathbb{Q}$; a section $aj_{\mathbb{Q}}$ of the base-changed designation over the base-changed curve; a morphism $k_{\mathbb{Q}}$ from the geometric generic pullback to the $\mathbb{Q}$-pullback, with `hkQ₁`, `hkQ₂` identifying its two components (the first projection is preserved, the second is the second projection followed by $\operatorname{Spec}$ of $\mathbb{Q} \to \overline{\mathbb{Q}}$); a morphism $\overline{aj} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ and a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base; `hpoinc`, an isomorphism between the Poincaré bundle of `hDQ` and the base change to $\mathbb{Q}$ of the pullback of the Poincaré bundle of `hD` along the first projection of $O.g$ with $\operatorname{Spec}\mathbb{Q}$; `hajQε`, that the zero section is carried to the zero section of the base-changed designation; `hajQ`, the Abel–Jacobi property of $aj_{\mathbb{Q}}$, namely that for every field $K$, every morphism $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every point $x$ of the base-changed curve over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $aj_{\mathbb{Q}}$ is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor of $t$ followed by the base-changed $\infty$-section; `hajbar`, that $\overline{aj}$ is `𝔛.eeta` followed by $k_{\mathbb{Q}}$, $aj_{\mathbb{Q}}$ and the first projection, together with `hajbar_over`, that it lies over the geometric generic point; `hεbar` and `hεbar_aj`, that $\overline{\varepsilon}$ is carried to the $\infty$-section and that $\overline{\varepsilon}$ followed by $\overline{aj}$ is the identity element of $O.L$ at the geometric generic point; `hpts_law`, that $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD` with the zero-group cut; and `hAJ`, that for all $\overline{\mathbb{Q}}$-points $x, s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base with $s$ equal to the $\infty$-section there is a degree-zero divisor $Dv$ on $\overline{F}_H$ equal to $(x) - (s)$ under the bijection `𝔛.Meta.pointEquivPlace` between such points and places, whose class satisfies $(O.\mathrm{pts}\,[Dv])_1 = x$ followed by $\overline{aj}$.
--
--   The inertia-fixed frame consists of a commutative domain $R$ which is a Henselian local ring with algebraically closed residue field, equipped with an $R$-algebra structure on $\overline{\mathbb{Q}}$ with faithful scalar multiplication, subject to: `hRA`, that $R$ maps into $\mathfrak{Pl}$; `hRdvr`, that $R$ is a discrete valuation ring; `hRirr`, that $p$ is irreducible in $R$; `hRfix`, that an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ lies in the inertia subgroup of $\mathfrak{Pl}$ precisely when it fixes the image of $R$ pointwise; and `hRmax`, that every element of $\mathfrak{Pl}$ fixed by that inertia subgroup comes from $R$.
--
--   The $p$-divisible group frame consists of a $p$-divisible group $\mathcal{G}$ over $R$ of height $h$ (a system of finite free commutative Hopf algebras `level v` of rank $p^{vh}$ with surjective transitions whose kernels are the $p^{v}$-torsion ideals), an additive map $\Delta$ from the points of $\mathcal{G}$ over $\overline{\mathbb{Q}}$ to $J_H(M)$, and: `hΔinj`, injectivity of $\Delta$; `hΔlev`, that for every $v$ the subgroup $O.\mathrm{finPts}(p^{v})$ — the subgroup of $J_H(M)$ generated by those $p^{v}$-torsion classes $y$ for which the predicate `ExtendsToPlace` holds for $\mathfrak{Pl}$, $\Lambda.\sigma_A$ and the section $O.\mathrm{pts}\,y$ — is exactly the image under $\Delta$ of the level-$v$ points; `hΔgal`, equivariance of $\Delta$ for automorphisms of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which are $R$-linear; and `hΔhecke`, that for every set $S$ and every generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) there is a family of coalgebra endomorphisms $\varphi_v$ of the levels of $\mathcal{G}$, compatible with the transition maps, inducing on points through $\Delta$ the Hecke or diamond operator `genOpH M H S g`.
--
--   Finally, $w_{\mathrm{gen}}$ is a semilinear automorphism of $\overline{F}_H$ over $\overline{\mathbb{Q}}$ (a pair of ring automorphisms of $\overline{F}_H$ and of $\overline{\mathbb{Q}}$ compatible with the structure map), and `hwgen` requires that whenever two $\overline{\mathbb{Q}}$-points $y, y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ satisfy that $y'$ transported to the model and followed by `𝔛.w.hom` agrees with $y$ so transported, the place of $y'$ is $w_{\mathrm{gen}}$ acting on the place of $y$; $W_{\mathrm{bar}}$ is an additive endomorphism of $J_H(M)$ with $W_{\mathrm{bar}} x = w_{\mathrm{gen}} \cdot x$ for all $x$ (`hWbar`). A ring homomorphism $\rho : R_p \to \mathfrak{Pl}$ is given with `hρ` saying that $\rho$ followed by the inclusion of $\mathfrak{Pl}$ is the structure map to $\overline{\mathbb{Q}}$, and `hσA` saying $\Lambda.\sigma_A = \operatorname{Spec}\rho$. The reduction dictionary `hsp` (summarised here) requires, for each $i \in \{0,1\}$, each pair of $\overline{\mathbb{Q}}$-points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$ together with $\mathfrak{Pl}$-sections $u_1, u_2$ of the level-$\Gamma_M$ model lifting them, with image in the smooth locus, with prescribed reductions $u_{\kappa,1}, u_{\kappa,2}$ to the fibre over the residue field and closed points $P_1, P_2$ of the special-fibre curve model whose images under `𝔛.efib` followed by the $i$-th component map are the closed points of those reductions, for the degree-zero divisor $Dv = (y_1) - (y_2)$, and for an admissible gluing datum $x$ for the finite set $O.\mathrm{ssFinset}$ of pairs of places whose first component is the difference of the places of $P_1$ and $P_2$ if $i = 0$ and zero otherwise, whose second component is that difference if $i = 1$ and zero otherwise, and whose third component vanishes: the existence of a section $s$ of $O.g$ over $\Lambda.\sigma_A$ with $(O.\mathrm{pts}\,[Dv])_1$ equal to `barPt Pl` followed by $s$ and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along `resPt Pl` equal to the class of $x$ in the glued Picard group.
--
--   Under these hypotheses the following holds. Let $x$ be an element of the $p$-torsion subgroup of $\mathrm{Pic}^0(\overline{\mathbb{Q}}, \overline{F}_H) = J_H(M)$ whose underlying class lies in $O.\mathrm{finPts}\,p$. Let $D$ be a degree-zero divisor on $\overline{F}_H$, let $f \in \overline{F}_H$ and let $y$ be a Laurent series over $\mathfrak{Pl}$ such that: the class of $D$ is $x$; $f \neq 0$; for every place $v$ of $\overline{F}_H$ over $\overline{\mathbb{Q}}$ one has $p \cdot (w_{\mathrm{gen}} \cdot D)(v) = \operatorname{ord}_v f$; the Laurent series of $f$ is the image of $y$ under coefficientwise application of the inclusion of $\mathfrak{Pl}$; and the coefficientwise reduction of $y$ to the residue field is non-zero. Let further $g$ be an element of $\overline{F} =$ `Fbar p M H hpM` (the $q$-expansion function field of level $\Gamma_N$ over the residue field of $\mathfrak{Pl}$) whose Laurent series is the coefficientwise reduction of $y$, and assume $p \mid \operatorname{ord}_v g$ for every place $v$ of $\overline{F}$ over the residue field.
--
--   Then there exist a section $s$ of $O.g$ over $\Lambda.\sigma_A$ and a degree-zero divisor $E$ on $\overline{F}$ over the residue field of $\mathfrak{Pl}$ such that: first, $(O.\mathrm{pts}(W_{\mathrm{bar}}\,x))_1 =$ `barPt Pl` followed by $s$; second, the class of $E$ in $\mathrm{Pic}^0$ equals the first component of the pair obtained by applying `GluedPic0.toPic0Pair O.ssFinset` to $O.\mathrm{ptsSp}^{-1}$ of `resPt Pl` followed by $s$; and third, for every place $v$ of $\overline{F}$ over the residue field, $p \cdot E(v) = \operatorname{ord}_v g$.
--
--   This is the Néron-model half of the Serre-type compatibility between the $p$-torsion of $J_H(M)$ and the special fibre at $p$: for a $p$-torsion class whose Néron section extends over the place $\mathfrak{Pl}$, the $\Sigma^{\infty}$-coordinate of the reduced section is computed as $\tfrac1p$ times the divisor of the reduction of the normalised root function of the Atkin–Lehner translate of the class. It feeds the construction of reduced root functions and the finite-part counting used in the level-lowering step, being cited by the assembled reduction statements for the glued Picard group at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_section_toPic0Pair_eq_mk_of_mem_finPts_of_forall_dvd_ord_tauFree.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_section_toPic0Pair_eq_mk_of_mem_finPts_of_forall_dvd_ord_tauFree
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
    ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∈ O.finPts p →
      ∀ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) → f ≠ 0 →
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) →
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y →
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
      ∀ g : ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl),
        (g : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y →
      (∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          (p : ℤ) ∣ v.ord g) →
      ∃ (s : NeronModelInfra.SchemeHomOver Λ.σA O.g)
        (E : AlgebraicCurve.Divisor.degZero (K := IsLocalRing.ResidueField ↥Pl) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))),
        (O.pts (Wbar ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H))).1 = ModularCurve.JZeroNeronObjectAtP.barPt Pl ≫ s.1 ∧
        AlgebraicCurve.Pic0.mk E =
          (AlgebraicCurve.GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨ModularCurve.JZeroNeronObjectAtP.resPt Pl, rfl⟩ s))).1 ∧
        ∀ v : AlgebraicCurve.Place (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl)),
          (p : ℤ) * (E : AlgebraicCurve.Divisor (IsLocalRing.ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥Pl))) v = v.ord g := by sorry
