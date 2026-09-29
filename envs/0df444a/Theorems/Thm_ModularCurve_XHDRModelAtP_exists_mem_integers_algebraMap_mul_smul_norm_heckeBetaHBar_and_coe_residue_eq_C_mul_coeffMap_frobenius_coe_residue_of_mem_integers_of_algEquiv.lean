-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
-- name    : ModularCurve.XHDRModelAtP.exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/58aaaa3a-8740-549d-8c28-582dcb7abfca
-- title:
--   Gauss residue of the Uₚ-pushed function is c·Frobenius
-- statement:
--   Throughout, $\bar F_H(M)$ denotes the geometric function field [`ModularCurve.xHFunctionFieldBar M H`](def/ModularCurve_XH.html#L123), that is the subfield of $\operatorname{LaurentSeries}(\overline{\mathbb Q})$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise image of the rational $q$-expansion field of level $(M,H)$; $J_H(M)$ denotes [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the group $\mathrm{Pic}^0(\overline{\mathbb Q},\bar F_H(M))$ of degree-zero divisor classes modulo principal divisors; $\kappa$ denotes `IsLocalRing.ResidueField ↥Pl`; `coeffMap` denotes coefficientwise application of a ring homomorphism to Laurent series; `HahnSeries.C c` the constant series $c$; and `qExpand` the substitution $q \mapsto q^{p}$ on Laurent series.
--
--   **Arithmetic data.** A prime $p$ with $p \neq 2$; a level $M \neq 0$ with $p \mid M$ and $p^{2} \nmid M$; a subgroup $H \le (\mathbb Z/M)^{\times}$ which, by `hHp`, contains every unit whose image under the reduction $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$ is $1$; a set $S \subseteq \mathbb N$. The hypothesis `hin` is [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): for every prime $\ell$ the predicate `HeckeInputsHAlong` holds over $\overline{\mathbb Q}$ for $(M,H,\ell)$, and for every $d \in (\mathbb Z/M)^{\times}$ there is an $\overline{\mathbb Q}$-algebra automorphism $\sigma$ of $\bar F_H(M)$ satisfying `IsDiamondAutHBar M H d σ`. Further, $Pl$ is a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that $p$ is a nonunit of $Pl$ (`hPl`), its residue field $\kappa$ being of characteristic $p$ and algebraically closed; $K$ is an algebraically closed field of characteristic $p$ over $\mathbb Z/p$; and `hj` asserts that the $j$-series [`ModularCurve.jqModC ℚ`](def/ModularCurve_JqCoeff.html#L15) lies in the $q$-expansion function field of level $\mathrm{SL}_2(\mathbb Z)$.
--
--   **Integral model and Néron data.** $\mathfrak X$ is a term of [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81): the two-chart integral model `toBase p (ΓM M H) hj` over $R(p)$ is proper, flat, integral and locally of finite presentation with integrally closed sections on affine opens, the model at level $\Gamma_N$ is proper and smooth of relative dimension $1$, and $\mathfrak X$ carries a curve model `𝔛.Meta` for $\bar F_H(M)$ over $\overline{\mathbb Q}$ together with an isomorphism `𝔛.eeta` onto the base change of the model to $\overline{\mathbb Q}$, pins relating places to geometric points Galois-equivariantly, pins identifying chart sections with $q$-expansions, an isomorphism `𝔛.w`, sections `𝔛.εinf`, `𝔛.π`, and the generic smoothness and geometric integrality assertions packaged in that structure. $\Lambda$ is level data [`ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl`](def/ModularCurve_JHNeronObjectAtP.html#L32) (a scheme over the base $\operatorname{Spec} R(p)$ with a relative group law and parametrisations of the generic and special points) and $O$ is a term of [`ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ`](def/ModularCurve_JHNeronObjectAtP.html#L53), a smooth separated group scheme $O.G \to \operatorname{Spec} R(p)$ with relative group law $O.L$, a bijection $O.\mathrm{pts} : J_H(M) \simeq$ (points over the geometric generic point), Galois and Hecke compatibilities, and the remaining fields of that structure.
--
--   **Relative Picard and Abel–Jacobi frame.** The following hypotheses, all relative to the `algEquivZeroCut` condition (fibrewise algebraic equivalence to zero of rigidified line bundles), are imposed: `hrepΛ`, that the designation built from $\Lambda.X$, $\Lambda.f$ and the unit section of $\Lambda.L$ represents the relative $\mathrm{Pic}^0$ subfunctor of the level-$\Gamma_N$ model with section `schemeHomOverComp 𝔛.εinf 𝔛.π`; `hD`, the same for the level-$\Gamma_M$ model with section `𝔛.εinf` and the designation built from $O.G$, $O.g$ and the unit section of $O.L$; `hDQ`, the corresponding representability after base change to $\mathbb Q$; `hsep`, separatedness of the generic fibre; `ajQ`, a morphism over $\mathbb Q$ from the generic curve to the base-changed Picard scheme; `kQ` together with `hkQ₁`, `hkQ₂`, a comparison between the fibre over the geometric generic point and the fibre over $\mathbb Q$ commuting with both projections up to $\operatorname{Spec}$ of $\mathbb Q \to \overline{\mathbb Q}$; `ajbar` with `hajbar` defining it as `𝔛.eeta` followed by `kQ`, `ajQ` and the first projection, and `hajbar_over` placing it over the generic point; `εbar`, a $\overline{\mathbb Q}$-point of `𝔛.Meta.C`, with `hεbar` saying it lies over `𝔛.εinf` and `hεbar_aj` saying that `ajbar` sends it to the unit section of $O.L$; `hpoinc`, an isomorphism between the Poincaré bundle of `hDQ` and the base change to $\mathbb Q$ of the pullback of the Poincaré bundle of `hD` along the first projection; `hajQε`, that the base-changed section followed by `ajQ` is the zero section of the base-changed designation; `hajQ`, the Abel–Jacobi property of `ajQ`, namely that for every field $K'$, every $\operatorname{Spec} K' \to \operatorname{Spec}\mathbb Q$ and every point $x$ of the generic curve over it, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor cut out by the section at infinity; `hpts_law`, that $O.\mathrm{pts}$ is additive for the relative group law attached to `hD`; and `hAJ`, that for all $\overline{\mathbb Q}$-points $x,s$ of `𝔛.Meta.C` with $s$ lying over `𝔛.εinf` there is a degree-zero divisor $D_v$ equal to $(\text{place of } x) - (\text{place of } s)$ whose class satisfies $O.\mathrm{pts}(\mathrm{Pic}^0\text{-class of } D_v) = x$ followed by `ajbar`.
--
--   **Coefficient ring and $p$-divisible group.** $R$ is a henselian local domain which is a discrete valuation ring (`hRdvr`) with algebraically closed residue field, equipped with an $R$-algebra structure on $\overline{\mathbb Q}$ with faithful scalar multiplication, such that: the image of $R$ lies in $Pl$ (`hRA`); $p$ is irreducible in $R$ (`hRirr`); an automorphism $\sigma$ of $\overline{\mathbb Q}$ over $\mathbb Q$ lies in the inertia subgroup of $Pl$ precisely when it fixes the image of $R$ pointwise (`hRfix`); and every $y \in Pl$ fixed by that inertia subgroup is in the image of $R$ (`hRmax`). Moreover $\mathcal G$ is a $p$-divisible group [`PDivisibleGroup R p h`](def/PDivisibleGroup_Basic.html#L199) (finite free cocommutative Hopf algebras `𝒢.level v` over $R$ of rank $p^{vh}$, surjective transition maps with kernel the $p^{v}$-torsion ideal), and $\Delta$ is an injective (`hΔinj`) additive map from $\mathcal G.\mathrm{Points}(\overline{\mathbb Q})$ to $J_H(M)$ such that: `hΔlev`, for every $v$ a class $y$ lies in $O.\mathrm{finPts}(p^{v})$ — the subgroup generated by the $p^{v}$-torsion classes whose point extends to the place — exactly when $y$ is the image under $\Delta$ of a level-$v$ point; `hΔgal`, $\Delta$ is equivariant for an automorphism $\tau$ of $\overline{\mathbb Q}$ over $\mathbb Q$ and any $R$-algebra automorphism $\tau'$ agreeing with it; and `hΔhecke`, for every set $S$ and every Hecke generator $g \in$ [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (a $T_\ell$, a $U_q$ or a diamond) there is a family of $R$-coalgebra endomorphisms $\varphi_v$ of the levels commuting with the transitions and inducing, through $\Delta$, the operator [`ModularCurve.genOpH M H S g`](def/ModularCurve_XHOperators.html#L80) on $J_H(M)$.
--
--   **Semilinear automorphism, reduction map and $p$-torsion expansions.** $w :=$ `wgen` is an element of `SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)`, i.e. a pair consisting of a ring automorphism of $\bar F_H(M)$ and one of $\overline{\mathbb Q}$ compatible with the structure map; `hwgen` requires that whenever two $\overline{\mathbb Q}$-points $y,y'$ of `𝔛.Meta.C` are related by `𝔛.w`, their places satisfy $\mathrm{place}(y') = w \cdot \mathrm{place}(y)$. Next, $\iota_K : Pl \to K$ is a ring homomorphism whose vanishing locus is exactly the set of elements of valuation $< 1$ (`hιK`). The map $\Psi$ assigns to each $p$-torsion class $x$ of $\mathrm{Pic}^0(\overline{\mathbb Q},\bar F_H(M))$ an element of the $q$-expansion function field over $K$ of level $\Gamma_H(M/p)$ with $H$ reduced, and `hΨ` requires for each such $x$ the existence of a degree-zero divisor $D$, a nonzero $f \in \bar F_H(M)$ and a Laurent series $y$ over $Pl$ with: the class of $D$ equal to $x$ in $J_H(M)$; $p\,(w\cdot D)(v) = v.\mathrm{ord}(f)$ at every place $v$; the Laurent series of $f$ equal to `coeffMap Pl.subtype y`; `coeffMap (residue) y ≠ 0`; and the Laurent series of $\Psi(x)$ over $K$ equal to `coeffMap ιK y`.
--
--   **Gauss prolongation.** $R_g$ is a `RegularProlongation` of $Pl$ from `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (GammaH M H))` to `qExpFunctionFieldC κ (GammaH M H)`: a valuation subring `Rg.integers` of the first field with a surjective residue homomorphism onto the second whose kernel is the maximal ideal, compatible with the residue map of $Pl$ and such that every nonzero element becomes integral with nonzero residue after scaling. Three pins are imposed: `hRg₁`, membership of $f$ in `Rg.integers` is equivalent to the existence of Laurent series $x,y$ over $Pl$ with `coeffMap (residue) y ≠ 0` and $f \cdot$ `coeffMap Pl.subtype y` $=$ `coeffMap Pl.subtype x`; `hRg₂`, every Laurent series over $Pl$ lying in the field is integral with residue `coeffMap (residue) y`; and `hRg₃`, for integral $f$ and $x,y$ as in `hRg₁` the residue of $f$ times `coeffMap (residue) y` equals `coeffMap (residue) x`.
--
--   **Diamond and Atkin–Lehner pins.** A unit $d \in (\mathbb Z/M)^{\times}$ whose reduction to $\mathbb Z/(M/p)$ equals $p$ (`hd`) and whose reduction, or the negative of that reduction, lies in [`ModularCurve.infSubgroup p M H hpM`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ under the reduction of unit groups (`hdH`). Finally $\theta$ is an $\overline{\mathbb Q}$-algebra automorphism of $\bar F_H(M)$ such that (`hθ`) whenever $f \in \bar F_H(M)$ has the same Laurent series as an element $u$ of the geometric function field of level $(M/p, \mathrm{infSubgroup})$, the Laurent series of $\theta(f)$ is `qExpand (AlgebraicClosure ℚ) p` applied to that of $u$; and `hwθ` requires $w =$ `SemilinearAut.ofAlgAut θ`, i.e. $w$ is the pair $(\theta, \mathrm{id})$.
--
--   **Conclusion.** For every $f \in \bar F_H(M)$ and every hypothesis `hf` that the image of $f$ in `laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (GammaH M H))` lies in `Rg.integers`, there exist $\lambda \in \overline{\mathbb Q}$ with $\lambda \neq 0$, a proof `hfU` that the element
--   $$\lambda \cdot \Bigl( w \cdot \mathrm{Norm}\bigl(\beta(w^{-1}\cdot f)\bigr) \Bigr) \in \bar F_H(M)$$
--   lies in `Rg.integers`, and an element $c$ of $\kappa$, such that $c \neq 0$ and
--   $$\bigl(R_g\text{-residue of that element}\bigr) \;=\; \mathrm{C}(c)\cdot \mathrm{coeffMap}\bigl(\mathrm{frobenius}\,\kappa\,p\bigr)\bigl(R_g\text{-residue of } f\bigr)$$
--   as Laurent series over $\kappa$. Here $\beta$ is `heckeBetaHBar (AlgebraicClosure ℚ) M H p`, mapping $\bar F_H(M)$ into the geometric top field at level $M p$, the norm is `Algebra.norm` for the algebra structure on that top field over $\bar F_H(M)$ given by [`AlgebraicCurve.algebraAlong`](def/AlgebraicCurve_Correspondence.html#L14) applied to `heckeAlphaHBar (AlgebraicClosure ℚ) M H p`, $w$ acts through its semilinear automorphism, and $\mathrm{frobenius}\,\kappa\,p$ is $x \mapsto x^{p}$ applied coefficientwise.
--
--   This is the residue-level (special-fibre) form, in the $w$-transport convention, of the statement that $U_p$ acts on $q$-expansions at $p \,\|\, M$ through the Frobenius of the component at infinity: the Gauss residue of the $U_p$-pushed function is a nonzero constant times the coefficientwise $p$-th power of the residue of $f$. It is used in the assembly of the reduced root function for $U_p$, a step in the mod-$p$ analysis of the Jacobian of $X_H(M)$ entering level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv.lean

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
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open ModularCurve in

theorem ModularCurve.XHDRModelAtP.exists_mem_integers_algebraMap_mul_smul_norm_heckeBetaHBar_and_coe_residue_eq_C_mul_coeffMap_frobenius_coe_residue_of_mem_integers_of_algEquiv
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

    [CharP K p]

    (Ψ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) → ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hΨ : ∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), ∃ (D : AlgebraicCurve.Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.xHFunctionFieldBar M H))) (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (y : LaurentSeries ↥Pl),
        AlgebraicCurve.Pic0.mk D = ((x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)) : ModularCurve.JH M H) ∧ f ≠ 0 ∧
        (∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
          (p : ℤ) * (wgen • (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))) v = v.ord f) ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap Pl.subtype y ∧
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
        ((Ψ x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) = ModularCurve.coeffMap ιK y)

    (Rg : AlgebraicCurve.RegularProlongation Pl ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H)))
    (hRg₁ : ∀ f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))), f ∈ Rg.integers ↔
        ∃ x y : LaurentSeries ↥Pl, ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 ∧
          (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x)
    (hRg₂ : ∀ (y : LaurentSeries ↥Pl) (hy : ModularCurve.coeffMap Pl.subtype y ∈ ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
        ∃ hO : (⟨ModularCurve.coeffMap Pl.subtype y, hy⟩ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers,
          ((Rg.residue ⟨_, hO⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) = ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y)
    (hRg₃ : ∀ (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hf : f ∈ Rg.integers) (x y : LaurentSeries ↥Pl),
        ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap Pl.subtype y = ModularCurve.coeffMap Pl.subtype x →
        ((Rg.residue ⟨f, hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) * ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) y =
          ModularCurve.coeffMap (IsLocalRing.residue ↥Pl) x)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)

    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H)) (u : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwθ : wgen = SemilinearAut.ofAlgAut θ)
    :
    ∀ (f : ↥(ModularCurve.xHFunctionFieldBar M H))
      (hf : (f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers),
      ∃ (lam : AlgebraicClosure ℚ) (hlam : lam ≠ 0)
        (hfU : ((algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) lam *
            (letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H p)
         wgen • (Algebra.norm ↥(ModularCurve.xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H p (wgen⁻¹ • f)) : ↥(ModularCurve.xHFunctionFieldBar M H))) : ↥(ModularCurve.xHFunctionFieldBar M H)) : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ∈ Rg.integers)
        (c : (IsLocalRing.ResidueField ↥Pl)), c ≠ 0 ∧
        ((Rg.residue ⟨_, hfU⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) =
          HahnSeries.C c *
            ModularCurve.coeffMap (frobenius (IsLocalRing.ResidueField ↥Pl) p) ((Rg.residue ⟨(f : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))), hf⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥Pl) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥Pl)) := by sorry
