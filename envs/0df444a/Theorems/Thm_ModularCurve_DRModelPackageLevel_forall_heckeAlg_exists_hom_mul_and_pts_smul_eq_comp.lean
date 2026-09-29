-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp
-- name    : ModularCurve.DRModelPackageLevel.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/07d5ca94-f240-57e5-bae6-5a8f3ee1fb7a
-- title:
--   Hecke algebra acts by homomorphic endomorphisms of D
-- statement:
--   Fix a prime $p$ and $N_0\ge 1$ with $p\nmid N_0$, and a level-$N_0p$ Deligne–Rapoport package $\mathfrak P$ on the Igusa model `toBase N₀ p` over $R_p$, assumed proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation for `toBase N₀ p` over $R_p$, i.e. a scheme $D.P$ with a structure morphism $D$`.toBase` to $\operatorname{Spec} R_p$ and a zero section, and let `hD` assert that $D$ represents the functor of line bundles on the curve rigidified along the cusp section $\mathfrak P$`.εinf` whose fibres over algebraically closed points are algebraically equivalent to zero (a Poincaré bundle satisfying the condition, a universal property, and triviality of its restriction along the zero section). Further hypotheses: $D$`.toBase` is smooth, separated, quasi-compact, surjective and geometrically connected; `hDQ`, the analogous representability over $\mathbf Q$ for the base change $D_{\mathbf Q}$ of $D$ along the curve's base change, together with `hPQ`, an isomorphism of its Poincaré bundle with the one induced from `hD`; an Abel–Jacobi morphism `ajQ` from the generic-fibre curve to $D_{\mathbf Q}$ over $\operatorname{Spec}\mathbf Q$, carrying the cusp section to the zero section, and such that for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}\mathbf Q$ and every $K$-point $x$ of the curve over $t$, the pullback of the Poincaré bundle along $x$ followed by `ajQ` is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of the cusp; a morphism `kQ` identifying the $\overline{\mathbf Q}$-fibre of the curve with the base change of the $\mathbf Q$-fibre along $\operatorname{Spec}\overline{\mathbf Q}\to\operatorname{Spec}\mathbf Q$, compatibly with both projections; the resulting morphism `ajbar` from the curve model $\mathfrak P$`.Meta.C` of $\overline{\mathbf Q}(X_0(N_0p))$ to $D.P$ (namely $\mathfrak P$`.eeta` followed by `kQ`, `ajQ` and the first projection), lying over $\mathfrak P$`.Meta.toBase` followed by `genPt p`; a $\overline{\mathbf Q}$-point `εbar` of $\mathfrak P$`.Meta.C` lying over the cusp section and sent by `ajbar` to the zero section; and a bijection `pts` from $\mathrm{Pic}^0$ of the field `modularFunctionFieldBar (N₀ * p)` onto the $\overline{\mathbf Q}$-points of $D$ over `genPt p` which is additive for the relative group law attached to `hD`, equivariant for $\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$ acting on $\operatorname{Spec}\overline{\mathbf Q}$, and normalised by `ajbar`: for all $\overline{\mathbf Q}$-points $x$ and $s$ of $\mathfrak P$`.Meta.C` with $s$ over the cusp, the degree-zero divisor $[x]-[s]$, read through the place dictionary of the curve model, has class whose image under `pts` is $x$ followed by `ajbar`. The conclusion, for the Hecke module structure `heckeModuleBar (N₀ * p)` on $\mathrm{Pic}^0$, is that for every $t$ in `HeckeAlg` $=\mathbf Z[X_\ell:\ell\text{ prime}]$ there is an endomorphism $\varphi$ of $D.P$ over the base which is a homomorphism for the relative group law on $T$-valued points (for every scheme $T$ and every $T\to$ `base p`, $\varphi$ composed after a product equals the product of the composites) and satisfies `pts` $(t\cdot x)=$ `pts` $(x)$ followed by $\varphi$ for every $x$.
--
--   This is the statement that the total Hecke algebra acts on the integral model $D$ of $J_0(N_0p)$ over $\mathbf Z_{(p)}$ by endomorphisms that are homomorphic for the relative group law and compatible, via the Abel–Jacobi dictionary `pts`, with the divisorial Hecke action on $\mathrm{Pic}^0$ of the modular function field over $\overline{\mathbf Q}$. It supplies the `hecke` field of the Néron-object package `JZeroNeronObjectAtP`, and is used in the construction of that package from a Deligne–Rapoport level model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

theorem ModularCurve.DRModelPackageLevel.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) :
    letI := heckeModuleBar (N₀ * p)
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero (N₀ * p), (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by sorry
