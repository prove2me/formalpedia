-- Prove2me | Theorems.Thm_ModularCurve_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator_toric_orthogonal_fin_of_abelJacobiPin_of_divisorialWeilPairingData_of_degeneracyData
-- name    : ModularCurve.perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator_toric_orthogonal_fin_of_abelJacobiPin_of_divisorialWeilPairingData_of_degeneracyData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/77b6ef90-76f0-5044-ba61-5f3774938bb3
-- title:
--   Weil pairing on J_H(M)[p]: bilinearity, perfectness, equivariance
-- statement:
--   Throughout, $M$ is a non-zero natural number, $H \le (\mathbb{Z}/M)^{\times}$, and $p$ is a prime with $p \mid M$ and $p^{2} \nmid M$; $J_H(M)$ denotes `JH M H`, the group $\mathrm{Pic}^{0}$ of degree-zero divisor classes of the field $\overline{\mathbb{Q}}\cdot F_H(M) =$ `xHFunctionFieldBar M H`, the $\overline{\mathbb{Q}}$-base change inside Laurent series of the level-$\Gamma_H(M)$ $q$-expansion function field, over the constant field $\overline{\mathbb{Q}}$.
--
--   The geometric input consists of: the hypothesis `hHp`, that every unit of $(\mathbb{Z}/M)^{\times}$ mapping to $1$ under the reduction map to $(\mathbb{Z}/(M/p))^{\times}$ lies in $H$; the hypothesis `hj`, that the $q$-expansion `jqModC ℚ` of $j$ lies in the level-$SL_2(\mathbb{Z})$ function field over $\mathbb{Q}$; a Deligne–Rapoport type integral model datum $\mathfrak{X}$ : `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the arithmetic local base ring $R_p$ at $p$, which carries among other things a curve model $\mathfrak{X}.\mathrm{Meta}$ of $\overline{\mathbb{Q}}\cdot F_H(M)$ together with an isomorphism $\mathfrak{X}.\mathrm{eeta}$ onto the $\overline{\mathbb{Q}}$-fibre of the model and a cusp section $\mathfrak{X}.\varepsilon_{\inf}$; a valuation subring $\mathfrak{P}$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $\mathfrak{P}$, whose residue field is algebraically closed of characteristic $p$; a level datum $\Lambda$ of level $M/p$ over $\mathfrak{P}$ (a scheme $\Lambda.X \to \operatorname{Spec} R_p$ with a relative group law $\Lambda.L$ and bijections $\Lambda.\mathrm{pts}$, $\Lambda.\mathrm{ptsSp}$ from $J_H(M/p)$, for the image subgroup `infSubgroup p M H hpM`, and from $\mathrm{Pic}^{0}$ of the special-fibre function field, onto the sections over the generic, respectively the special, point); and a Néron-type object $O$ : `JHNeronObjectAtP p M H hpM Pl hPl Λ`, with smooth separated group scheme $O.G \to \operatorname{Spec} R_p$, commutative relative group law $O.L$, a bijection $O.\mathrm{pts}$ from $J_H(M)$ onto the sections over the generic point, Hecke operators and the subgroups $O.\mathrm{toricPts}\,p$ and $O.\mathrm{finPts}\,p$ of $J_H(M)$.
--
--   The representability and Abel–Jacobi hypotheses are: `hD`, that the designation formed from $O.G$, $O.g$ and the unit section represents, over $R_p$, the part of the relative Picard functor of $\mathfrak{X}$ rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ and cut out by the condition `algEquivZeroCut` (fibrewise algebraic equivalence to zero), i.e. it carries a Poincaré bundle with the corresponding universal property and triviality along the zero section; `hDQ`, the same after base change to $\mathbb{Q}$; `hsep`, separatedness of the $\mathbb{Q}$-fibre of the model; an Abel–Jacobi morphism $\mathrm{ajQ}$ from the $\mathbb{Q}$-fibre of the model to the base-changed designation, a comparison morphism $kQ$ between the pullbacks of the model along the generic point and along $\operatorname{Spec}\mathbb{Q}$, a morphism $\overline{\mathrm{aj}} : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ and a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$ of $\mathfrak{X}.\mathrm{Meta}.C$, subject to: `hpoinc` (the Poincaré bundle of `hDQ` is isomorphic to the base change to $\mathbb{Q}$ of a pullback of that of `hD`), `hajQε` (the cusp section composed with $\mathrm{ajQ}$ is the zero section), `hajQ` (for every field $K$, every $\mathbb{Q}$-point $t$ of it and every $K$-point $x$ of the $\mathbb{Q}$-fibre, the pullback of the Poincaré bundle along $x$ followed by $\mathrm{ajQ}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of the cusp section at $t$, i.e. it represents the class of $x-\varepsilon$), `hkQ₁` and `hkQ₂` (compatibility of $kQ$ with the two projections, the second up to $\operatorname{Spec}$ of $\mathbb{Q} \to \overline{\mathbb{Q}}$), `hajbar` (that $\overline{\mathrm{aj}}$ is the composite of $\mathfrak{X}.\mathrm{eeta}$, $kQ$, $\mathrm{ajQ}$ and the first projection), `hajbar_over` (that $\overline{\mathrm{aj}}$ lies over the generic point), `hεbar` and `hεbar_aj` (that $\overline{\varepsilon}$ is the cusp point and is sent by $\overline{\mathrm{aj}}$ to the identity section), `hpts_law` (that $O.\mathrm{pts}$ is additive for the relative group law obtained from `hD`), and `hAJ`, the Abel–Jacobi pin: for all $\overline{\mathbb{Q}}$-points $x$ and $s$ of $\mathfrak{X}.\mathrm{Meta}.C$ with $s$ the cusp point, there is a degree-zero divisor whose underlying divisor is $[\mathrm{place}(x)] - [\mathrm{place}(s)]$ and whose class is carried by $O.\mathrm{pts}$ to $x$ followed by $\overline{\mathrm{aj}}$.
--
--   The pairing data are: a divisorial Weil pairing datum $e$ of level $p$ on $\overline{\mathbb{Q}}\cdot F_H(M)$ (a map `pair` on pairs of $p$-torsion classes of $\mathrm{Pic}^{0}$ with values in $\overline{\mathbb{Q}}$, agreeing with the divisorial pairing $\prod f_{D_1}(D_2)/\prod f_{D_2}(D_1)$ of every Weil datum of level $p$, together with a moving property producing, for each torsion class and each finite set of places, a representing degree-zero divisor supported at rational places outside that set); an arbitrary function $B : J_H(M) \times J_H(M) \to \overline{\mathbb{Q}}$; and the hypothesis `hB` that $B(x,y) = e.\mathrm{pair}(x,y)$ whenever $(p:\mathbb{Z})\cdot x = 0$ and $(p:\mathbb{Z})\cdot y = 0$. Further, $p \neq 2$ is assumed (`hp2`).
--
--   The level-$(M/p)$ and degeneracy data are: `hrepΛ`, representability of the corresponding sub-Picard functor for the level-$\Gamma_N(p,M,H)$ model, rigidified along the cusp section composed with $\mathfrak{X}.\pi$, by the designation built from $\Lambda.X$, $\Lambda.f$ and the unit section; existence of principal divisors for the level-$(M/p)$ field; `hΛ`, the abelian-scheme property bundle for $\Lambda.f$ (smooth, proper, connected fibres, and a relative group law); `hΛpts_add` and `hΛptsSp_add`, additivity of $\Lambda.\mathrm{pts}$ and of $\Lambda.\mathrm{ptsSp}$ (the latter through the base change of $\Lambda.L$ to the special point); two $\overline{\mathbb{Q}}$-algebra maps $\alpha_H, \beta_H$ from the level-$(M/p)$ function field to the level-$M$ one, each assumed integral and to satisfy the fundamental identity, finiteness and the pushforward norm formula (`hαHint`, `hαHFI`, `hαHfin`, `hαHN`, and likewise for $\beta_H$); `hdeg0` and `hdeg1`, that $O.\mathrm{degPts}\,0$ and $O.\mathrm{degPts}\,1$ send the class of a degree-zero divisor $D$ to the class of its pushforward along $\alpha_H$, respectively along $\beta_H$; additive endomorphisms $F$, $F^{-1}$, $F^{*}$ of $\mathrm{Pic}^{0}$ of the special-fibre function field with `hF` ($F$ is the $q$-expansion Frobenius pushforward mod $p$ at level $\Gamma_N(p,M,H)$), `hFinv` ($F$ and $F^{-1}$ are mutually inverse) and `hFstar` ($F^{*} = p \cdot F^{-1}$); a unit $pb$ of $\mathbb{Z}/(M/p)$ with value $p$ (`hpb`) and the endomorphism $\delta$ given by the diamond action mod $p$ of the $\Gamma_0$-lift of $pb$ (`hδ`); and degeneracy maps $\alpha_{\mathrm{pull}} : \mathrm{Fin}\,2 \to (J_H(M/p) \to_{+} J_H(M))$ together with morphisms $\mathrm{degPull} : \mathrm{Fin}\,2 \to \mathrm{SchemeHomOver}\,\Lambda.f\,O.g$, subject to `hpull` (compatibility on generic-fibre points), `hpull_mul` (each $\mathrm{degPull}\,i$ is compatible with the two group laws), `hpullsp` (on the special fibre, `GluedPic0.toPic0Pair` over $O.\mathrm{ssFinset}$ of the point obtained by composing with $\mathrm{degPull}\,i$ equals $(x, F^{*}x)$ for $i=0$ and $(F^{*}x, \delta x)$ for $i=1$, where $x$ is the class corresponding to the given special-fibre point), and `hpullα`, `hpullβ` (that $\alpha_{\mathrm{pull}}\,0$ and $\alpha_{\mathrm{pull}}\,1$ are divisor pullback along $\alpha_H$, respectively along $\beta_H$, on classes of degree-zero divisors).
--
--   Under these hypotheses, eleven assertions hold, all of them about $B$ restricted to elements killed by $p$.
--
--   First, $B(x,y)^{p} = 1$ for all $x,y$ with $p\cdot x = 0 = p\cdot y$, so the values lie in the group of $p$-th roots of unity. Second, $B(x+x',y) = B(x,y)\,B(x',y)$ for $p$-torsion $x, x', y$. Third, $B(x,y+y') = B(x,y)\,B(x,y')$ for $p$-torsion $x, y, y'$. Fourth, left non-degeneracy: if $p \cdot x = 0$ and $B(x,y) = 1$ for every $p$-torsion $y$, then $x = 0$.
--
--   Fifth, Galois equivariance: for every $\sigma \in \mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $p$-torsion $x,y$, $B(\sigma\cdot x, \sigma\cdot y) = \sigma(B(x,y))$.
--
--   Sixth, Hecke adjointness: for every prime $\ell$, given integrality of `heckeAlphaHBar` and of `heckeBetaHBar` at level $M$, $H$, $\ell$, existence of principal divisors for the $\overline{\mathbb{Q}}$-base change of the level-$(M,H,M\ell)$ function field, the fundamental identity for `heckeAlphaHBar`, and finiteness together with the norm formula for `heckeBetaHBar`, one has for all $p$-torsion $x,y$
--   $$B\bigl(T_\ell x,\;y\bigr) = B\bigl(x,\;T_\ell^{t} y\bigr),$$
--   where $T_\ell$ is `heckeOperatorHAlong` (the Hecke correspondence on $\mathrm{Pic}^{0}$ at level $\Gamma_H(M)$, set to $0$ when the required inputs fail) and $T_\ell^{t}$ is `heckePic0HBarTranspose`, the correspondence given by pullback along `heckeAlphaHBar` followed by pushforward along `heckeBetaHBar`.
--
--   Seventh, diamond adjointness: for every $d \in (\mathbb{Z}/M)^{\times}$ and all $p$-torsion $x,y$, $B(\langle d\rangle x, y) = B(x, \langle d^{-1}\rangle y)$, where $\langle d \rangle$ is `diamondHBar M H d`, the additive endomorphism of $J_H(M)$ induced by the semilinear automorphism attached to the diamond automorphism of the function field.
--
--   Eighth, right non-degeneracy: if $p\cdot y = 0$ and $B(x,y) = 1$ for every $p$-torsion $x$, then $y = 0$.
--
--   Ninth, the double-annihilator property: for every additive subgroup $A \le J_H(M)$ all of whose elements are killed by $p$, and every $x$ with $p\cdot x = 0$ such that $B(x,y) = 1$ holds for every $p$-torsion $y$ annihilating $A$ (that is, with $B(a,y)=1$ for all $a \in A$), one has $x \in A$.
--
--   Tenth, toric–finite orthogonality: $B(x,y) = 1$ for all $x \in O.\mathrm{toricPts}\,p$ (the subgroup generated by the toric points of $O$ at level $p$) and all $y \in O.\mathrm{finPts}\,p$ (the subgroup generated by those $p$-torsion classes whose associated point extends to the place attached to $\mathfrak{P}$ and $\Lambda.\sigma_A$).
--
--   Eleventh, antisymmetry: $B(x,y)\,B(y,x) = 1$ for all $p$-torsion $x,y$.
--
--   This is the package of standard properties of the Weil pairing on the $p$-torsion of the Jacobian of $X_H(M)$ in the case $p \parallel M$: $\mu_p$-values, bilinearity, two-sided non-degeneracy, Galois equivariance, adjointness for the Hecke and diamond operators, the double-annihilator property, orthogonality of the toric and finite parts at a place above $p$, and antisymmetry. It is used in the analysis of the $p$-torsion of $J_H(M)$ at $p$, notably by the results producing a perfect pairing on an idempotent-cut corner with its Galois and radical data, and by the counting of toric and finite points in such a corner, both steps on the way to Ribet's level-lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator_toric_orthogonal_fin_of_abelJacobiPin_of_divisorialWeilPairingData_of_degeneracyData.lean

import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups in
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve in
open ModularCurve in

theorem ModularCurve.perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator_toric_orthogonal_fin_of_abelJacobiPin_of_divisorialWeilPairingData_of_degeneracyData
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
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

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) p)
    (B : JH M H → JH M H → AlgebraicClosure ℚ)
    (hB : ∀ (x y : JH M H) (hx : (p : ℤ) • x = 0) (hy : (p : ℤ) • y = 0),
      B x y = e.pair ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩)

    (hp2 : p ≠ 2)

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))
    [NeZero (M / p)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))]
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (ModularCurve.JZeroNeronObjectAtP.baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt Pl ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαHint : αH.toRingHom.IsIntegral) (hαHFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) αH hαHint)
    (hαHfin : FiniteAlong (AlgebraicClosure ℚ) αH) (hαHN : NormFormulaAlong (AlgebraicClosure ℚ) αH hαHfin)
    (hβHint : βH.toRingHom.IsIntegral) (hβHFI : FundamentalIdentityAlong (AlgebraicClosure ℚ) βH hβHint)
    (hβHfin : FiniteAlong (AlgebraicClosure ℚ) βH) (hβHN : NormFormulaAlong (AlgebraicClosure ℚ) βH hβHfin)
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαHint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
        (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβHint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
        O.degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)
    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ModularCurve.XHDRLevel.ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))
    (hpullα : ∀ Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      αpull 0 (Pic0.mk Dw) = Pic0.mk ⟨Divisor.pullbackAlong αH hαHint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        Divisor.pullbackAlong_mem_degZero αH hαHint hαHFI Dw.2⟩)
    (hpullβ : ∀ Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
      αpull 1 (Pic0.mk Dw) = Pic0.mk ⟨Divisor.pullbackAlong βH hβHint (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        Divisor.pullbackAlong_mem_degZero βH hβHint hβHFI Dw.2⟩) :
    (∀ x y : JH M H, p • x = 0 → p • y = 0 → B x y ^ p = 1) ∧
    (∀ x x' y : JH M H, p • x = 0 → p • x' = 0 → p • y = 0 → B (x + x') y = B x y * B x' y) ∧
    (∀ x y y' : JH M H, p • x = 0 → p • y = 0 → p • y' = 0 → B x (y + y') = B x y * B x y') ∧
    (∀ x : JH M H, p • x = 0 → (∀ y : JH M H, p • y = 0 → B x y = 1) → x = 0) ∧

    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : JH M H), p • x = 0 → p • y = 0 → B (σ • x) (σ • y) = σ (B x y)) ∧

    (∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
        [HasPrincipalDivisors (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
        (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
        (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
        (hNβ : NormFormulaAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
        (x y : JH M H), p • x = 0 → p • y = 0 →
        B (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) y =
          B x (heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ y)) ∧

    (∀ (d : (ZMod M)ˣ) (x y : JH M H), p • x = 0 → p • y = 0 →
        B (diamondHBar M H d x) y = B x (diamondHBar M H d⁻¹ y)) ∧

    (∀ y : JH M H, p • y = 0 → (∀ x : JH M H, p • x = 0 → B x y = 1) → y = 0) ∧

    (∀ A : AddSubgroup (JH M H), (∀ a ∈ A, p • a = 0) →
      ∀ x : JH M H, p • x = 0 →
        (∀ y : JH M H, p • y = 0 → (∀ a ∈ A, B a y = 1) → B x y = 1) → x ∈ A) ∧

    (∀ x ∈ O.toricPts p, ∀ y ∈ O.finPts p, B x y = 1) ∧

    (∀ x y : JH M H, p • x = 0 → p • y = 0 → B x y * B y x = 1) := by sorry
