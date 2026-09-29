-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp
-- name    : ModularCurve.XHDRModelAtP.ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/4111cbd1-70a7-5c4a-8149-c503f64e5709
-- title:
--   Special-fibre formula for the degeneracy push-forwards at p ∥ M
-- statement:
--   Fix a prime $p$ and a level $M$, a subgroup $H\le(\mathbb Z/M)^\times$, and divisibility hypotheses `hpM : p ∣ M` and `hpM2 : ¬ p^2 ∣ M`, so that $p$ exactly divides $M$; assume `hHp`, that every unit of $\mathbb Z/M$ whose image under `ZMod.unitsMap` in $(\mathbb Z/(M/p))^\times$ is trivial lies in $H$, and `hj`, that the $q$-series `jqModC ℚ` lies in the $q$-expansion function field of the full level over $\mathbb Q$. Let $\mathfrak X$ be a term of `XHDRModelAtP p M H hpM hj`, that is, an integral model over `R p` of the curve of level `ΓM M H` together with its special-fibre data (in particular the section at infinity $\mathfrak X.\varepsilon_{\mathrm{inf}}$, the degeneracy morphism $\mathfrak X.\pi$ to level `ΓN p M H hpM`, the Atkin–Lehner involution $\mathfrak X.w$, the curve model $\mathfrak X.\mathrm{Meta}$ of the geometric generic fibre with its identification $\mathfrak X.\mathrm{eeta}$, the smooth locus $\mathfrak X.\mathrm{smoothLocus}$, and the special-fibre curve model $\mathfrak X.\mathrm{Mfib}$ with its maps $\mathfrak X.\mathrm{efib}$ and component maps $\mathfrak X.\mathrm{comp}$). Properness and separatedness of the integral models at levels `ΓM M H` and `ΓN p M H hpM` are available as instance hypotheses.
--
--   Level-$M$ Picard data. $D$ is a relative $\mathrm{Pic}^0$ designation over `R p` for `toBase p (ΓM M H) hj`, i.e. a scheme with a structure morphism to $\operatorname{Spec}(R p)$ and a zero section; `hD` asserts that $D$ represents the relative rigidified Picard functor cut out by the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut` with rigidification along $\mathfrak X.\varepsilon_{\mathrm{inf}}$ (so $D$ carries a Poincaré bundle and the universal property, hence a relative group law). `hDQ` is the corresponding representability statement after base change to $\mathbb Q$, for `D.baseChange ℚ` rigidified along the base-changed section, and `hPQ` identifies the Poincaré bundle of `hDQ` with the base change to $\mathbb Q$ of the pullback of the Poincaré bundle of `hD` along the first projection. The morphism `ajQ` is an Abel–Jacobi map over $\mathbb Q$ from the generic fibre to `(D.baseChange ℚ).toBase`; `hajQε` says it carries the section at infinity to the zero section, and `hajQ` is its pinning: for every field $K$, every $K$-point $t$ of $\operatorname{Spec}\mathbb Q$ and every point $x$ of the base-changed curve over $t$, the pullback of the Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of the point $x$ tensored with the ideal module of the divisor cut out by the section at infinity over $t$. The morphism `kQ` compares the pullbacks of `toBase p (ΓM M H) hj` along `genPt p` and along `specMap (R p) ℚ`, with `hkQ₁` and `hkQ₂` the two projection compatibilities (the second involving $\operatorname{Spec}$ of $\mathbb Q\to\overline{\mathbb Q}$). The morphism `ajbar` from $\mathfrak X.\mathrm{Meta}.C$ to $D.P$ is defined by `hajbar` as $\mathfrak X.\mathrm{eeta}$ followed by `kQ`, `ajQ` and the first projection; `hajbar_over` says it lies over `genPt p`. The pair `εbar` is a $\overline{\mathbb Q}$-point of $\mathfrak X.\mathrm{Meta}.C$ with `hεbar` identifying it with the section at infinity and `hεbar_aj` saying that `ajbar` sends it to the zero section. Finally `pts` is a bijection from $J_H(M)=\mathrm{Pic}^0$ of the level-$M$ function field over $\overline{\mathbb Q}$ to the $\overline{\mathbb Q}$-points of $D$, additive for the relative group law of `hD` (`hpts_add`), and pinned by `hpts_aj`: for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ lying over the section at infinity there is a degree-zero divisor equal to the difference of the places attached to $x$ and to $s$ whose class is carried by `pts` to $x$ followed by `ajbar`.
--
--   Residual and level-$(M/p)$ data. $A$ is a valuation subring of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime p` (that is, $p$ is a non-unit of $A$), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and $\rho : R p \to A$ is a ring homomorphism compatible with the structure map to $\overline{\mathbb Q}$ (`hρ`). $D_0$ is a relative $\mathrm{Pic}^0$ designation for `toBase p (ΓN p M H hpM) hj`, and `hD₀` asserts that it represents the analogous functor rigidified along $\mathfrak X.\varepsilon_{\mathrm{inf}}$ followed by $\mathfrak X.\pi$. The maps $\alpha_H,\beta_H$ are $\overline{\mathbb Q}$-algebra maps from the level-$(M/p)$ function field (for `infSubgroup p M H hpM`, the image of $H$) to the level-$M$ function field, integral by `hαint`, `hβint`; `Meta₀` is a curve model of the level-$(M/p)$ function field over $\overline{\mathbb Q}$, with an isomorphism `eeta₀` onto the base change of the level-`ΓN` model to $\overline{\mathbb Q}$ satisfying `heeta₀`, and the two dictionaries `hMeta₀π`, `hMeta₀πw` state that a point of `Meta₀` lying under a point $y$ of $\mathfrak X.\mathrm{Meta}.C$ via $\mathfrak X.\pi$ (respectively via $\mathfrak X.w$ followed by $\mathfrak X.\pi$) has place the restriction along $\alpha_H$ (respectively $\beta_H$) of the place of $y$. The two homomorphisms `degPts 0`, `degPts 1` from $J_H(M)$ to $J_{H'}(M/p)$ are pinned by `hdeg0`, `hdeg1` as the divisor push-forwards along $\alpha_H$ and along $\beta_H$ on classes. The hypotheses `hDQ₀`, `hPQ₀`, `ajQ₀`, `hajQ₀ε`, `hajQ₀`, `kQ₀`, `hkQ₀₁`, `hkQ₀₂`, `ajbar₀`, `hajbar₀`, `hajbar₀_over`, `εbar₀`, `hεbar₀`, `hεbar₀_aj`, `pts₀`, `hpts₀_add`, `hpts₀_aj` repeat, verbatim one level down for $D_0$, `Meta₀`, `eeta₀` and the section $\mathfrak X.\varepsilon_{\mathrm{inf}}$ followed by $\mathfrak X.\pi$, the Picard representability, Poincaré comparison, Abel–Jacobi and point-dictionary package just described.
--
--   Special-fibre dictionaries. `ptsSp₀` is a bijection from $\mathrm{Pic}^0$ of `Fbar p M H hpM κ`, the $q$-expansion function field of level `ΓN p M H hpM` over $\kappa$, to the points of $D_0$ over `resPt A` followed by $\operatorname{Spec}\rho$; it is additive for the base-changed group law of `hD₀` (`hptsSp₀_add`) and pinned by `hptsSp₀`: given two $A$-points $v_1,v_2$ of the level-`ΓN` model, their $\kappa$-fibre points $v_{\kappa,1},v_{\kappa,2}$ (compatible with the two projections), closed points $Q_1,Q_2$ of $\mathfrak X.\mathrm{Mfib}$ whose images under $\mathfrak X.\mathrm{efib}$ are the closed points of those fibre points, and a degree-zero divisor $D_w$ equal to the difference of the places of $Q_1$ and $Q_2$, there exists an $A$-point $s_0$ of $D_0$ whose Poincaré pullback is isomorphic to the line bundle of $v_1$ tensored with the ideal module of $v_2$, and whose restriction to $\kappa$ is carried by `ptsSp₀.symm` to the class of $D_w$.
--
--   Further, `SS` is a finite set of pairs of places of `Fbar p M H hpM κ`, $t$ a natural number, `ptsSp` a bijection from the glued Picard group `GluedPic0 κ (Fbar …) SS` (classes of admissible gluing data — a pair of degree-zero divisors vanishing at the first, respectively second, coordinates of the pairs in `SS`, together with a family of units of $\kappa$ indexed by `SS` — modulo glued principal data) to the points of $D$ over `resPt A` followed by $\operatorname{Spec}\rho$; `abq 0`, `abq 1` are morphisms from the $\kappa$-base change of $D$ to that of $D_0$; $\tau$ is a point of the $\kappa$-base change of $D$ over the split torus `torusStr κ t`; and $B$ is an isomorphism from the character lattice of `SS` (the kernel of the total-degree map on $\mathbb Z^{SS}$) onto $\mathbb Z^{t}$. The hypothesis `hS` is a conjunction of fourteen clauses, summarised here: `SS` is exactly the set `ssNodePairsQExp κ (ΓN p M H hpM) p` of supersingular node pairs; $t+1$ is the cardinality of `SS`; `ptsSp` is additive for the base-changed group law of `hD`; an Abel–Jacobi pin for `ptsSp` stating that for each $i\in\{0,1\}$, a pair of $A$-points $u_1,u_2$ of the level-$M$ model with image in $\mathfrak X.\mathrm{smoothLocus}$, together with their $\kappa$-fibre points, closed points $P_1,P_2$ of $\mathfrak X.\mathrm{Mfib}$ matching them through $\mathfrak X.\mathrm{efib}$ followed by the $i$-th component map, and an admissible gluing datum whose $i$-th divisor component is the difference of the places of $P_1$ and $P_2$, the other divisor component and the unit component being zero, is realised by an $A$-point $s$ of $D$ with Poincaré pullback the line bundle of $u_1$ tensored with the ideal module of $u_2$ and with `ptsSp.symm` of its $\kappa$-restriction the given glued class; each `abq i` is a homomorphism for the base-changed group laws; the morphism $(\mathrm{abq}\,0,\mathrm{abq}\,1)$ into the fibre product is flat and surjective; a point of the $\kappa$-base change of $D$ is killed by both `abq i` precisely when it factors through $\tau$; each `abq i` commutes with composition by base automorphisms $\sigma$; `ptsSp₀.symm` of `abq i` applied to `ptsSp x` is the first or second component of `GluedPic0.toPic0Pair SS x` according as $i=0$ or $i=1$; $\tau$ is a closed immersion; $\tau$ transforms products of characters into the group law; the image of $\tau$ meets `ptsSp x` exactly when $x$ lies in the range of `GluedPic0.nodeUnit SS`; and, for a character $\chi$ and a family of units $w$ indexed by `SS`, the point of $\tau$ at $\chi$ equals the fibre point of `ptsSp (GluedPic0.nodeUnit SS w)` if and only if for every element $a$ of the character lattice the product $\prod_s w(s)^{a(s)}$ equals $\chi$ of the monomial $B(a)$.
--
--   Finally, $\delta_0,\delta_1$ are morphisms from $D$ to $D_0$ over $\operatorname{Spec}(R p)$ such that `hδmul`: each $\delta_i$ is a homomorphism for the relative group laws attached to `hD` and `hD₀` on points over any base; and `hδpts`: for each $i$ and each $x\in J_H(M)$, the point $\mathrm{pts}_0(\mathrm{degPts}\,i\,x)$ equals $\mathrm{pts}(x)$ followed by $\delta_i$.
--
--   Conclusion. For every unit $\bar e\in(\mathbb Z/(M/p))^\times$ with $\bar e\cdot p=1$ in $\mathbb Z/(M/p)$, and every point $x$ of $D$ over `resPt A` followed by $\operatorname{Spec}\rho$, the following two identities hold in $\mathrm{Pic}^0$ of `Fbar p M H hpM κ`, read through `ptsSp₀.symm`:
--   $$\mathrm{ptsSp}_0^{-1}(x\circ\delta_0)=\mathrm{ptsSp}_0^{-1}(\mathrm{abq}\,0\,(x))+F\bigl(\mathrm{ptsSp}_0^{-1}(\mathrm{abq}\,1\,(x))\bigr),$$
--   $$\mathrm{ptsSp}_0^{-1}(x\circ\delta_1)=F\bigl(\mathrm{ptsSp}_0^{-1}(\mathrm{abq}\,0\,(x))\bigr)+\langle\bar e\rangle\cdot\mathrm{ptsSp}_0^{-1}(\mathrm{abq}\,1\,(x)),$$
--   where $x\circ\delta_i$ denotes $x$ followed by $\delta_i$, $\mathrm{abq}\,i\,(x)$ denotes `fibreMap (abq i) x`, $F$ is the Frobenius push-forward `qExpFrobeniusPushforwardModL κ (ΓN p M H hpM) p` on $\mathrm{Pic}^0$, and $\langle\bar e\rangle$ is the semilinear automorphism `SemilinearAut.ofAlgAut` of the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the lift [`CuspForm.gammaLift (M/p) ē`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) of $\bar e$ to $\Gamma_0(M/p)$, acting on $\mathrm{Pic}^0$.
--
--   This is the Eichler–Shimura–Deligne–Rapoport description, in the form used by Ribet, of the two degeneracy push-forwards from level $M$ to level $M/p$ on the special fibre at $p$ of the Picard object, expressed through the toric/abelian decomposition of the glued special fibre: one degeneracy map is identity plus Frobenius, the other Frobenius plus the diamond operator $\langle p^{-1}\rangle$. It supplies the clause on degeneracy morphisms used by [`ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special`](thm.html#ModularCurve.XHDRModelAtP.exists_degeneracyHom_mul_pts_special), and thereby the local input at $p\parallel M$ for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_JacJ1Iface
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

set_option maxHeartbeats 800000 in

theorem ModularCurve.XHDRModelAtP.ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    [IsProper (toBase p (ΓN p M H hpM) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (αH βH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hαint : αH.toRingHom.IsIntegral) (hβint : βH.toRingHom.IsIntegral)
    (Meta₀ : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (eeta₀ : Meta₀.C ⟶ pullback (toBase p (XHDRLevel.ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))))
    [IsIso eeta₀]
    (heeta₀ : eeta₀ ≫ pullback.snd _ _ = Meta₀.toBase)
    (hMeta₀π : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong αH hαint (𝔛.Meta.pointEquivPlace y))
    (hMeta₀πw : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}) (y₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      y₀.1 ≫ eeta₀ ≫ pullback.fst _ _ = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom ≫ 𝔛.π.1 →
      Meta₀.pointEquivPlace y₀ = Place.restrictAlong βH hβint (𝔛.Meta.pointEquivPlace y))
    (degPts : Fin 2 → (JH M H →+ JH (M / p) (infSubgroup p M H hpM)))
    (hdeg0 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong αH hαint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 0 (Pic0.mk Dv) = Pic0.mk Dw)
    (hdeg1 : ∀ (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) (Dw : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))),
      (Dw : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) = Divisor.pushforwardAlong βH hβint (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) →
      degPts 1 (Pic0.mk Dv) = Pic0.mk Dw)

    (hDQ₀ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π))) (D₀.baseChange ℚ))
    (hPQ₀ : Nonempty (hDQ₀.poincare.L ≅ (BaseChange.ofR (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) ℚ
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ₀ : SchemeHomOver (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (D₀.baseChange ℚ).toBase)
    (hajQ₀ε : (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1 ≫ ajQ₀.1 = (D₀.baseChange ℚ).zeroSection)
    (hajQ₀ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ)),
      Nonempty ((hDQ₀.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ₀.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ₀.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓN p M H hpM) hj) ℚ) (t ≫ (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ₀ : pullback (toBase p (ΓN p M H hpM) hj) (genPt p) ⟶ pullback (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ))
    (hkQ₀₁ : kQ₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p))
    (hkQ₀₂ : kQ₀ ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓN p M H hpM) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar₀ : Meta₀.C ⟶ D₀.P) (hajbar₀ : ajbar₀ = eeta₀ ≫ kQ₀ ≫ ajQ₀.1 ≫ pullback.fst D₀.toBase (specMap (R p) ℚ))
    (hajbar₀_over : ajbar₀ ≫ D₀.toBase = Meta₀.toBase ≫ genPt p)
    (εbar₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _})
    (hεbar₀ : εbar₀.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1)
    (hεbar₀_aj : εbar₀.1 ≫ ajbar₀ = genPt p ≫ D₀.zeroSection)

    (pts₀ : JH (M / p) (infSubgroup p M H hpM) ≃ SchemeHomOver (genPt p) D₀.toBase)
    (hpts₀_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM),
      pts₀ (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul _ (pts₀ x) (pts₀ y))
    (hpts₀_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta₀.C // q ≫ Meta₀.toBase = 𝟙 _}),
      s.1 ≫ eeta₀ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) =
          Finsupp.single (Meta₀.pointEquivPlace x) 1 - Finsupp.single (Meta₀.pointEquivPlace s) 1 ∧
        (pts₀ (Pic0.mk Dv)).1 = x.1 ≫ ajbar₀)
    (ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase)

    (hptsSp₀_add : ∀ a b, ptsSp₀ (a + b) =
      ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
        (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b))))

    (hptsSp₀ : ∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    [IsSeparated (toBase p (ΓM M H) hj)]
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
        Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (t : ℕ)
    (ptsSp : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS ≃
      SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)
    (abq : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase))
    (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase))
    (B : characterLattice ↥SS ≃+ (Fin t → ℤ))
    (hS :
      (∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p) ∧
      t + 1 = SS.card ∧

      (∀ x y, ptsSp (x + y) =
        ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
          (toFibrePt (ptsSp x)) (toFibrePt (ptsSp y)))) ∧

      (∀ (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (x : ↥(GluingData.admissible SS))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS).2.2 = 0),
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hD.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
        ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk SS x) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)),
        NeronModelInfra.schemeHomOverComp (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul s x y) (abq i) =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul s
            (NeronModelInfra.schemeHomOverComp x (abq i)) (NeronModelInfra.schemeHomOverComp y (abq i))) ∧
      Flat (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      Surjective (pullback.lift (abq 0).1 (abq 1).1 ((abq 0).2.trans (abq 1).2.symm)) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (x : SchemeHomOver s (RelativeGroupLaw.baseChangeStr (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase)),
        (∀ i, NeronModelInfra.schemeHomOverComp x (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).one s) ↔
          ∃ y : SchemeHomOver s (torusStr (ResidueField ↥A) t), NeronModelInfra.schemeHomOverComp y τ = x) ∧
      (∀ (σ : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))) (i : Fin 2)
        (x : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase),
        fibreMap (abq i) (GoodReductionJacobian.schemeHomOverComp σ.1 σ.2 x) =
          GoodReductionJacobian.schemeHomOverComp σ.1 σ.2 (fibreMap (abq i) x)) ∧

      (∀ (x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS) (i : Fin 2),
        ptsSp₀.symm (fibreMap (abq i) (ptsSp x)) =
          if i = 0 then (GluedPic0.toPic0Pair SS x).1 else (GluedPic0.toPic0Pair SS x).2) ∧

      IsClosedImmersion τ.1 ∧
      (∀ χ χ' : WithConv (torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A),
        NeronModelInfra.schemeHomOverComp (torusPt _ _ (χ * χ').ofConv) τ =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).baseChange (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _
            (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ.ofConv) τ)
            (NeronModelInfra.schemeHomOverComp (torusPt _ _ χ'.ofConv) τ)) ∧
      (∀ x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) SS,
        (∃ y : SchemeHomOver (𝟙 _) (torusStr (ResidueField ↥A) t),
            NeronModelInfra.schemeHomOverComp y τ = toFibrePt (ptsSp x)) ↔
          x ∈ (GluedPic0.nodeUnit SS).range) ∧

      (∀ (χ : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A)
          (w : ↥SS → Additive (ResidueField ↥A)ˣ),
        NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) t χ) τ =
            toFibrePt (ptsSp (GluedPic0.nodeUnit SS w)) ↔
          ∀ a : characterLattice ↥SS,
            ((∏ s, Additive.toMul (w s) ^ (a : ↥SS → ℤ) s : (ResidueField ↥A)ˣ) : ResidueField ↥A) =
              χ (AddMonoidAlgebra.single (B a) 1)))

    (δ : Fin 2 → SchemeHomOver D.toBase D₀.toBase)
    (hδmul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) (δ i) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s
            (NeronModelInfra.schemeHomOverComp x (δ i)) (NeronModelInfra.schemeHomOverComp y (δ i)))
    (hδpts : ∀ (i : Fin 2) (x : JH M H), (pts₀ (degPts i x)).1 = (pts x).1 ≫ (δ i).1) :
    (∀ (ē : (ZMod (M / p))ˣ), ((ē : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
      ∀ x : SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        ptsSp₀.symm (NeronModelInfra.schemeHomOverComp x (δ 0)) =
            ptsSp₀.symm (fibreMap (abq 0) x) +
              qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (ptsSp₀.symm (fibreMap (abq 1) x)) ∧
        ptsSp₀.symm (NeronModelInfra.schemeHomOverComp x (δ 1)) =
            qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p (ptsSp₀.symm (fibreMap (abq 0) x)) +
              SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) ē)) •
                ptsSp₀.symm (fibreMap (abq 1) x)) := by sorry
