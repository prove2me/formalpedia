-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne
-- name    : ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/3031a647-c611-5210-8156-3433c17dfbea
-- title:
--   Hecke operator T_ℓ, ℓ≠ p, on relative Pic⁰
-- statement:
--   Fix a prime $p$ and $N_0\ge 1$ with $p\nmid N_0$, and a Deligne–Rapoport package $\mathfrak P$ of level $N_0p$ on the Igusa model `toBase N₀ p` over $R_p$, assumed proper. Let $D$ be a relative $\mathrm{Pic}^0$ designation for this curve (a scheme $D.P$ over $\operatorname{Spec}R_p$ with a zero section) and let `hD` witness that $D$, with its Poincaré bundle, represents the subfunctor of the $\mathfrak P.\varepsilon_{\inf}$-rigidified relative Picard functor cut out by fibrewise algebraic equivalence to zero; assume $D.\mathrm{toBase}$ smooth, separated, quasi-compact, surjective and geometrically connected. Assume further: `hDQ`, the same representability for the base change to $\mathbb Q$, together with an isomorphism `hPQ` identifying its Poincaré bundle with the transport to $\mathbb Q$ of the pullback of `hD.poincare` along the first projection of $D.P\times_{R_p}\mathbb Q$; an Abel–Jacobi morphism $\mathrm{aj}_{\mathbb Q}$ from the generic fibre of the curve to $D_{\mathbb Q}$ taking the cusp section to the zero section and satisfying, for every field $K$, every $t:\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every $K$-point $x$ over $t$, an isomorphism between the pullback of the Poincaré bundle along $x$ followed by $\mathrm{aj}_{\mathbb Q}$ and $\mathcal L((x))\otimes I((\infty))$, the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of the cusp; a morphism $k_{\mathbb Q}$ from the $\overline{\mathbb Q}$-fibre to the $\mathbb Q$-fibre of the curve compatible with both projections, the second up to $\operatorname{Spec}\overline{\mathbb Q}\to\operatorname{Spec}\mathbb Q$; the induced morphism $\overline{\mathrm{aj}}$ from the curve model $\mathfrak P.\mathrm{Meta}.C$ to $D.P$, equal to $\mathfrak P.\mathrm{eeta}$ followed by $k_{\mathbb Q}$, $\mathrm{aj}_{\mathbb Q}$ and the first projection, lying over `genPt p`; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak P.\mathrm{Meta}.C$ mapping to the cusp $\mathfrak P.\varepsilon_{\inf}$ and to the zero section under $\overline{\mathrm{aj}}$; and a bijection `pts` from $J_0$ at level $N_0p$, i.e. the group of degree-zero divisor classes of the function field `modularFunctionFieldBar (N₀ * p)` over $\overline{\mathbb Q}$, onto the $\overline{\mathbb Q}$-points of $D$ over `genPt p`, additive for the relative group law supplied by `hD`, equivariant for $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and normalised by $\overline{\mathrm{aj}}$ in the sense that for any two $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak P.\mathrm{Meta}.C$ with $s$ the cusp there is a degree-zero divisor equal to $(x)-(s)$ under the point-to-place bijection whose class is sent by `pts` to $x$ followed by $\overline{\mathrm{aj}}$. Then for every prime $\ell\ne p$ there is an endomorphism $\varphi$ of $D$ over the base which is a homomorphism for the relative group law on $T$-valued points, for every scheme $T$ and morphism $s:T\to$ `base p`, and which induces `heckeOperatorBar (N₀ * p) ℓ`: for all $x$, `pts` of $T_\ell x$ is `pts x` followed by $\varphi$.
--
--   This realises the divisorial Hecke operator $T_\ell$ at a prime $\ell\ne p$ on $J_0(N_0p)(\overline{\mathbb Q})$ as a group-law endomorphism of the scheme representing the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model over $\mathbb Z_{(p)}$, the integral structure needed to compare Hecke actions on the Néron model and its special fibre. It is the generator step for [`ModularCurve.DRModelPackageLevel.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp`](thm.html#ModularCurve.DRModelPackageLevel.forall_heckeAlg_exists_hom_mul_and_pts_smul_eq_comp), which assembles the whole Hecke algebra action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne.lean

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

theorem ModularCurve.DRModelPackageLevel.exists_hom_mul_and_pts_heckeOperatorBar_eq_comp_of_ne
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
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) :
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero (N₀ * p), (pts (heckeOperatorBar (N₀ * p) ℓ x)).1 = (pts x).1 ≫ φ.1 := by sorry
