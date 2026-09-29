-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/28dea9ac-cba3-529a-a92c-d91d1b4c9d09
-- title:
--   Push-down and reduction agree on level-(M/p) dictionaries
-- statement:
--   Setting. Fix a prime $p$ and $M\neq 0$ with $p\mid M$ (`hpM`) and $p^{2}\nmid M$ (`hpM2`), a subgroup $H\le(\mathbb Z/M)^{\times}$ satisfying `hHp`: every unit $u$ with $\mathrm{unitsMap}\,u=1$ for the reduction $(\mathbb Z/M)^{\times}\to(\mathbb Z/(M/p))^{\times}$ lies in $H$; also $M/p\neq0$. The hypothesis `hj` says that the $q$-expansion `jqModC ℚ` of $j$ lies in the full-level field `qExpFunctionFieldC ℚ ⊤`; it is what makes the two-chart integral models `toBase p Γ hj` over `Spec (R p)` available. Write $H'=$ `infSubgroup p M H hpM` for the image of $H$ under the reduction map, `xHFunctionFieldBar M H` for the level-$M$ function field over $\overline{\mathbb Q}$, `JH M H` and `JH (M/p) H'` for the corresponding degree-zero divisor class groups $\mathrm{Pic}^{0}$, and `Fbar p M H hpM κ` for the level-$\Gamma_N(p,M,H)$ $q$-expansion field over a field $\kappa$.
--
--   Model data. `𝔛 : XHDRModelAtP p M H hpM hj` is the integral-model bundle at $p$: among its fields are a proper flat integral level-$\Gamma_M$ model and a proper smooth relative-dimension-one level-$\Gamma_N$ model over `Spec (R p)`, a curve model `𝔛.Meta` over $\overline{\mathbb Q}$ with function field `xHFunctionFieldBar M H` together with an isomorphism `𝔛.eeta` of `𝔛.Meta.C` onto the geometric generic fibre of the level-$\Gamma_M$ model (compatibly with the structure maps, and Galois-equivariantly on places), a section `𝔛.εinf` of the level-$\Gamma_M$ model over the identity of `Spec (R p)`, morphisms `𝔛.π` and `𝔛.πw` over the base from the level-$\Gamma_M$ to the level-$\Gamma_N$ model, a datum `𝔛.w` whose underlying morphism `𝔛.w.hom` is an endomorphism of the level-$\Gamma_M$ model, and, for a valuation subring presented as below, a special-fibre curve model `𝔛.Mfib A hA ρ hρ` with a morphism `𝔛.efib A hA ρ hρ` to the special fibre. It is assumed that `toBase p (ΓM M H) hj` is proper and that `toBase p (ΓN p M H hpM) hj` is proper and separated.
--
--   The place. $A$ is a valuation subring of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime p`, i.e. $p$ lies in the non-units of $A$, whose residue field $\kappa=$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed; $\rho : R_p\to A$ is a ring map with `hρ` asserting that $\rho$ followed by the inclusion $A\hookrightarrow\overline{\mathbb Q}$ is the structure map $R_p\to\overline{\mathbb Q}$.
--
--   Representability of relative $\mathrm{Pic}^{0}$. $D_0$ is a relative $\mathrm{Pic}^{0}$ designation for the level-$\Gamma_N$ model over $R_p$: a scheme `D₀.P` with a structure morphism `D₀.toBase` to `Spec (R p)` and a zero section. The datum `hD₀` asserts that $D_0$ represents the relative rigidified Picard functor of the level-$\Gamma_N$ model, rigidified along the section `schemeHomOverComp 𝔛.εinf 𝔛.π` and cut out by `algEquivZeroCut` (fibrewise algebraic equivalence to zero): it supplies a Poincaré rigidified line bundle lying in the cut, the universal property that every rigidified bundle in the cut is the pullback of the Poincaré bundle along a unique point of `D₀.toBase`, and the triviality of the pullback along the zero section.
--
--   Degeneracy on function fields and on classes. $\alpha_H,\beta_H$ are $\overline{\mathbb Q}$-algebra maps from the level-$(M/p)$ field `xHFunctionFieldBar (M/p) H'` to `xHFunctionFieldBar M H`, integral by `hαint`, `hβint`. The maps `degPts : Fin 2 → (JH M H →+ JH (M/p) H')` are pinned by `hdeg0` and `hdeg1`: whenever a degree-zero divisor $D_w$ on the level-$(M/p)$ field equals the divisor push-forward `Divisor.pushforwardAlong` of a degree-zero divisor $D_v$ along $\alpha_H$ (resp. $\beta_H$), then $\mathrm{degPts}\,0\,[D_v]=[D_w]$ (resp. $\mathrm{degPts}\,1\,[D_v]=[D_w]$).
--
--   Generic level-$(M/p)$ curve model. `Meta₀` is a curve model over $\overline{\mathbb Q}$ with function field `xHFunctionFieldBar (M/p) H'`, `eeta₀` an isomorphism from `Meta₀.C` onto the geometric generic fibre of the level-$\Gamma_N$ model with `heeta₀` saying that `eeta₀` followed by the second projection is `Meta₀.toBase`. The hypotheses `hMeta₀π` and `hMeta₀πw` identify places: for $\overline{\mathbb Q}$-points $y$ of `𝔛.Meta` and $y_0$ of `Meta₀`, if $y_0$ lands (through `eeta₀` and the first projection) on the image of $y$ under `𝔛.eeta`, the first projection and `𝔛.π.1` (resp. `𝔛.w.hom` followed by `𝔛.π.1`), then the place of $y_0$ is the restriction `Place.restrictAlong` of the place of $y$ along $\alpha_H$ (resp. $\beta_H$).
--
--   Abel–Jacobi data over $\mathbb Q$ and at the generic point. `hDQ₀` asserts that the base change of $D_0$ to $\mathbb Q$ represents the corresponding functor for the base-changed curve with the base-changed section, and `hPQ₀` that its Poincaré bundle is isomorphic to the transport along `BaseChange.ofR` of the pullback of the Poincaré bundle of `hD₀` along the first projection. `ajQ₀` is a morphism from the $\mathbb Q$-base-changed curve to the base of the base-changed designation with `hajQ₀ε` (the section composes to the zero section) and `hajQ₀`: for every field $K$, every $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every point $x$ of the curve over $t$, the pullback of the Poincaré bundle along $x$ followed by `ajQ₀` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of the divisor of $t$ followed by the base-changed section; so `ajQ₀` classifies $[x]-[\varepsilon]$. The morphism `kQ₀` compares the pullbacks over $\overline{\mathbb Q}$ and over $\mathbb Q$, with `hkQ₀₁`, `hkQ₀₂` fixing its two components. The morphism `ajbar₀ : Meta₀.C ⟶ D₀.P` is given by `hajbar₀` as `eeta₀`, `kQ₀`, `ajQ₀.1` and the first projection composed in this order, lies over `genPt p` by `hajbar₀_over`, and `εbar₀` is a $\overline{\mathbb Q}$-point of `Meta₀` which by `hεbar₀` corresponds to the cusp `genPt p ≫ 𝔛.εinf.1 ≫ 𝔛.π.1` and by `hεbar₀_aj` is sent by `ajbar₀` to the zero section.
--
--   The two dictionaries. `pts₀` is a bijection from `JH (M/p) H'` onto the $\overline{\mathbb Q}$-points of `D₀.toBase` over `genPt p`, additive for the relative group law attached to `hD₀` with the `algEquivZeroGroupCut` condition (`hpts₀_add`), and normalised by `hpts₀_aj`: for all $\overline{\mathbb Q}$-points $x,s$ of `Meta₀` with $s$ corresponding to the cusp as above, there is a degree-zero divisor $D_v$ on the level-$(M/p)$ field equal to $[\text{place of }x]-[\text{place of }s]$ with $(\mathrm{pts}_0[D_v])_1 = x$ followed by `ajbar₀`. `ptsSp₀` is a bijection from $\mathrm{Pic}^{0}$ of `Fbar p M H hpM κ` onto the points of `D₀.toBase` over `resPt A ≫ Spec.map ρ`, additive for the base change of that relative group law along `resPt A ≫ Spec.map ρ` in fibre coordinates (`hptsSp₀_add`), and normalised by `hptsSp₀`: given two $A$-sections $v_1,v_2$ of the level-$\Gamma_N$ model over $\operatorname{Spec}\rho$, their reductions $v_{\kappa,1},v_{\kappa,2}$ to the special fibre (sections of the fibre over $\kappa$ whose first components are the reductions of $v_1,v_2$), closed points $Q_1,Q_2$ of `𝔛.Mfib A hA ρ hρ` whose images under `𝔛.efib A hA ρ hρ` are the closed points carried by $v_{\kappa,1},v_{\kappa,2}$, and a degree-zero divisor $D_w$ on `Fbar p M H hpM κ` equal to $[\text{place of }Q_1]-[\text{place of }Q_2]$, there exists an $A$-point $s_0$ of `D₀.toBase` over $\operatorname{Spec}\rho$ such that the pullback of the Poincaré bundle of `hD₀` along $s_0$ is isomorphic to the line bundle of the divisor of $v_1$ tensored with the ideal module of the divisor of $v_2$, and $\mathrm{ptsSp}_0^{-1}$ of the reduction of $s_0$ to $\kappa$ equals $[D_w]$.
--
--   Conclusion. Under these hypotheses, for every $i\in\{0,1\}$ the following holds. Let $y_1$ be a $\overline{\mathbb Q}$-point of `𝔛.Meta`, $u_1$ an $A$-section of the level-$\Gamma_M$ model over $\operatorname{Spec}\rho$ whose restriction along `barPt A` is the point of the generic fibre determined by $y_1$ through `𝔛.eeta` and the first projection, $u_{\kappa,1}$ a $\kappa$-point of the special fibre of the level-$\Gamma_M$ model at $(\mathrm{residue}\,A)\circ\rho$ whose first component is the reduction of $u_1$ and whose second component is the identity, and $Q_1$ a closed point of `𝔛.Mfib A hA ρ hρ` whose image under `𝔛.efib A hA ρ hρ` is the closed point of $\kappa$ carried by $u_{\kappa,1}$ followed by `fibreMap` of `𝔛.π` if $i=0$ and of `𝔛.πw` if $i\neq0$; let $y_2,u_2,u_{\kappa,2},Q_2$ be a second such family, subject to the same four conditions. Let $D_v$ be a degree-zero divisor on `xHFunctionFieldBar M H` equal to $[\text{place of }y_1]-[\text{place of }y_2]$ and $D_w$ a degree-zero divisor on `Fbar p M H hpM κ` equal to $[\text{place of }Q_1]-[\text{place of }Q_2]$. Then there exists an $A$-point $s_0$ of `D₀.toBase` over $\operatorname{Spec}\rho$ such that
--
--   (i) $(\mathrm{pts}_0(\mathrm{degPts}\,i\,[D_v]))_1 = \mathrm{barPt}\,A$ followed by $s_0$, that is, the generic dictionary point of the pushed-down class $\mathrm{degPts}\,i\,[D_v]$ is the generic-fibre restriction of $s_0$; and
--
--   (ii) $\mathrm{ptsSp}_0^{-1}$ applied to the composite of `resPt A` with $s_0$ equals $[D_w]$, that is, the reduction of $s_0$ to $\kappa$ is the special dictionary point of the class of $[Q_1]-[Q_2]$.
--
--   This is the specialisation compatibility for the level-$(M/p)$ Jacobian at a prime $p$ exactly dividing $M$: a difference of $\overline{\mathbb Q}$-points of the level-$M$ curve which extends to $A$-sections has its image under either degeneracy map ($\pi$, resp. $\pi$ after the Atkin–Lehner datum) represented by a single $A$-point of the representing scheme $D_0$, whose generic restriction is the push-forward class and whose reduction is the corresponding divisor class on the special fibre. It is the conjunct used in assembling the level data for the Néron object at $p$, and is cited by [`ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords`](thm.html#ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_dictionary_of_xHDRModelAtP_torusCoords) and by [`ModularCurve.XHDRModelAtP.ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp`](thm.html#ModularCurve.XHDRModelAtP.ptsSp_levelN_symm_schemeHomOverComp_degeneracyHom_eq_of_pts_levelN_degPts_eq_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
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
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_levelN_degPts_eq_and_ptsSp_levelN_symm_eq_mk
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]
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
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw) :
    ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        (pts₀ (degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw := by sorry
