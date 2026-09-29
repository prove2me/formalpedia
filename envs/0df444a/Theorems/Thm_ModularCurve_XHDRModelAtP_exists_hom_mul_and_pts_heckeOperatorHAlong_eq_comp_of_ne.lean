-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne
-- name    : ModularCurve.XHDRModelAtP.exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/7ea4d61f-cc81-5567-a826-7e2047c2969a
-- title:
--   Hecke operators at ℓ≠ p on a relative Pic⁰ of X_H(M)
-- statement:
--   Fix a prime $p$ and a nonzero modulus $M$ with $p\mid M$ but $p^2\nmid M$, a subgroup $H\le(\mathbb Z/M)^\times$ containing the kernel of the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$, with $M/p$ nonzero, and assume $j$ lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb Z)$ (hypothesis `hj`), so that the two-chart integral model $X$ of level $\Gamma_M(M,H)$ over the discrete valuation ring `R p` with fraction field $\mathbb Q$ is available; let $\mathfrak X$ be a bundle of data `XHDRModelAtP p M H hpM hj` for it (properness, flatness, integrality and finite presentation of the structure morphism `toBase`, normality of its affine sections, a curve model `𝔛.Meta` over $\overline{\mathbb Q}$ for the function field $\bar F_H=$`xHFunctionFieldBar M H` together with an isomorphism `𝔛.eeta` onto the geometric generic fibre, Galois compatibility and chart pinning), and assume `toBase` proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation over `R p`: a scheme $D.P$ with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec}$`R p` and a zero section. Assume: $D$ represents, via `hD`, the functor of line bundles on $X$ rigidified along the section $\mathfrak X.\varepsilon_{\inf}$ and subject to the cut `algEquivZeroCut` (fibrewise algebraic equivalence to zero), i.e. there is a Poincaré bundle on $D$ satisfying the cut, universal for bundles satisfying it, and trivial along the zero section; $D.\mathrm{toBase}$ is smooth, separated, quasi-compact, surjective and geometrically connected; the base change $D_{\mathbb Q}$ likewise represents the corresponding cut for $X_{\mathbb Q}$ with the base-changed section (`hDQ`), its Poincaré bundle being isomorphic to the transport to $\mathbb Q$ of the pullback of the Poincaré bundle of `hD` along the first projection of $D_{\mathbb Q}$ (`hPQ`); there is an Abel–Jacobi morphism $\mathrm{aj}_{\mathbb Q}\colon X_{\mathbb Q}\to D_{\mathbb Q}$ over $\operatorname{Spec}\mathbb Q$ carrying the base-changed $\varepsilon_{\inf}$ to the zero section, and such that for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every point $x$ of $X_{\mathbb Q}$ over $t$, the pullback of the Poincaré bundle of `hDQ` along $x$ followed by $\mathrm{aj}_{\mathbb Q}$ is isomorphic to the dual of the ideal sheaf of the graph of $x$ tensored with the ideal sheaf of the graph of $t$ followed by the section, i.e. classifies $\mathcal O(x-\varepsilon_{\inf})$; a morphism $k_{\mathbb Q}$ from the geometric generic fibre to the generic fibre of $X$ compatible with both projections (the second up to $\operatorname{Spec}\mathbb Q\to\operatorname{Spec}\overline{\mathbb Q}$); the composite $\overline{\mathrm{aj}}=\mathfrak X.\mathrm{eeta}$ followed by $k_{\mathbb Q}$, $\mathrm{aj}_{\mathbb Q}$ and the first projection, a morphism $\mathfrak X.\mathrm{Meta}.C\to D.P$ lying over $\mathfrak X.\mathrm{Meta}.\mathrm{toBase}$ followed by the geometric generic point `genPt p`; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.\mathrm{Meta}.C$ mapping into $\varepsilon_{\inf}$ and sent by $\overline{\mathrm{aj}}$ to the zero section; and a bijection $\mathrm{pts}$ from $J_H(M)=\mathrm{Pic}^0(\overline{\mathbb Q},\bar F_H)$ onto the $\overline{\mathbb Q}$-points of $D$ which is additive for the relative group law attached to `hD`, equivariant for $\operatorname{Aut}(\overline{\mathbb Q}/\mathbb Q)$, and normalised by Abel–Jacobi: for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ lying over $\varepsilon_{\inf}$ there is a degree-zero divisor equal to the difference of the places of $x$ and $s$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\overline{\mathrm{aj}}$. Then for every prime $\ell\neq p$ there exists an endomorphism $\varphi$ of $D$ over $\operatorname{Spec}$`R p` which is a homomorphism for the relative group law (for every scheme $T$ with $s\colon T\to$ `base p` and all $T$-points $x,y$ of $D$, composing $x\cdot y$ with $\varphi$ equals $(x\circ\varphi)\cdot(y\circ\varphi)$) and which induces `heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ` on points: for every $x\in J_H(M)$, $\mathrm{pts}$ of its image under that operator equals $\mathrm{pts}(x)$ followed by $\varphi$.
--
--   This is the statement that the Hecke operator at a prime $\ell\neq p$ ($T_\ell$, or $U_\ell$ when $\ell\mid M$) on $J_H(M)$ extends to a group-law-preserving endomorphism of the scheme over `R p` representing the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_H(M)$ at $p$, compatibly with the dictionary between $\overline{\mathbb Q}$-points and divisor classes. It supplies the Hecke action in the construction of the Néron-type object [`ModularCurve.JHNeronObjectAtP`](def/ModularCurve_JHNeronObjectAtP.html#L53) attached to $J_H(M)$ at $p$; the operators $U_p$ and the diamond operators are treated separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups
set_option maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

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
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JH M H, (pts (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x)).1 = (pts x).1 ≫ φ.1 := by sorry
