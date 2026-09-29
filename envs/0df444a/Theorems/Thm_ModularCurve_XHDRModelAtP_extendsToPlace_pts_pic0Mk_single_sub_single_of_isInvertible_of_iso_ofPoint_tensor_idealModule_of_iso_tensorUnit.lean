-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_pic0Mk_single_sub_single_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit
-- name    : ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_single_sub_single_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/f68472b1-f635-5382-bbee-df632b2ab816
-- title:
--   Trivialised line bundle on mathfrak X_A makes pts([y₁]-[y₂]) extend
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb Z/M)^{\times}$, and $\mathrm{hj}$ witnessing that `jqModC ℚ` lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb Z)$; let $\mathfrak X$ be a `XHDRModelAtP p M H hpM hj`, with `toBase p (ΓM M H) hj` proper. The data comprise: a relative $\mathrm{Pic}^0$ designation $D$ over $R p$ for this curve (a scheme $D.P$ with structure map $D.\mathrm{toBase}$ and a zero section), witnesses $hD$, $hD_{\mathbb Q}$ that $D$ and its base change to $\mathbb Q$ represent the sub-Picard functor cut out by the condition `FibrewiseAlgEquivZero` on line bundles rigidified along $\mathfrak X.\varepsilon_{\inf}$; an isomorphism $hP_{\mathbb Q}$ between the $\mathbb Q$-Poincaré bundle and the base change of the Poincaré bundle over $R p$; an Abel–Jacobi morphism $aj_{\mathbb Q}$ over the $\mathbb Q$-fibre with $\varepsilon_{\inf} \mapsto$ zero section, whose pullback of the Poincaré bundle at any point $x$ over a field is $\mathcal O(x) \otimes \mathcal I(\infty)$ (the line bundle of `RelEffCartierDiv.ofPoint` at $x$ tensored with the ideal module of `ofPoint` at the $\infty$-section); a comparison map $k_{\mathbb Q}$ between the geometric generic fibre and the $\mathbb Q$-fibre, compatible with both projections up to $\mathbb Q \hookrightarrow \overline{\mathbb Q}$; $\overline{aj} = \mathfrak X.\mathrm{eeta} \circ$ ($k_{\mathbb Q}$ then $aj_{\mathbb Q}$ then the first projection), a morphism $\mathfrak X.\mathrm{Meta}.C \to D.P$ over $\mathrm{genPt}\ p$; a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.\mathrm{Meta}.C$ lying over $\mathfrak X.\varepsilon_{\inf}$ and mapped by $\overline{aj}$ to the zero section; and a bijection $\mathrm{pts}$ from $J_H = \mathrm{Pic}^0(\overline{\mathbb Q}, \mathrm{xHFunctionFieldBar}\ M\ H)$ onto the $\overline{\mathbb Q}$-points of $D.P$ over $\mathrm{genPt}\ p$ which is additive for the relative group law of $hD$, Galois-equivariant, and compatible with $\overline{aj}$: for all $\overline{\mathbb Q}$-points $x, s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ over $\varepsilon_{\inf}$ there is a degree-zero divisor equal to $[\,\mathrm{place}(x)\,] - [\,\mathrm{place}(s)\,]$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $\overline{aj}$. Further, $A$ is a valuation subring of $\overline{\mathbb Q}$ with $p$ in `A.nonunits`, whose residue field has characteristic $p$ and is algebraically closed; $\rho : R p \to A$ is a ring map with $A \hookrightarrow \overline{\mathbb Q}$ after $\rho$ equal to the structure map $R p \to \overline{\mathbb Q}$; $\psi$ and $\beta$ are the morphisms $\mathrm{barPt}\ A$ and $\mathrm{resPt}\ A$ viewed over $\mathrm{Spec}\,\rho$. Finally $y_1, y_2$ are $\overline{\mathbb Q}$-points of $\mathfrak X.\mathrm{Meta}.C$, with images $\bar y_1, \bar y_2$ in the curve over $\mathrm{genPt}\ p$ under $\mathfrak X.\mathrm{eeta}$ followed by the first projection, and $L$ is a module on $\mathfrak X_A =$ the pullback of `toBase` along $\mathrm{Spec}\,\rho$ which is invertible (locally isomorphic to the unit), whose pullback to the geometric generic fibre along $\psi$ is isomorphic to the line bundle of `ofPoint` at $\bar y_1$ tensored with the ideal module of `ofPoint` at $\bar y_2$, and whose pullback along each of the two morphisms $\mathfrak X.\mathrm{comp}\ A\ hA\ \rho\ h\rho\ i$ ($i :$ `Fin 2`) followed by the base-change map induced by $\beta$ is isomorphic to the unit module on the fibre of the level-$\Gamma_N$ curve over the residue field of $A$; and $[\,\mathrm{place}(y_1)\,] - [\,\mathrm{place}(y_2)\,]$ has degree zero. The conclusion is `ExtendsToPlace`: the $\overline{\mathbb Q}$-point $\mathrm{pts}$ of the class of this degree-zero divisor factors as $\mathrm{barPt}\ A$ followed by some morphism $\mathrm{Spec}\,A \to D.P$ over $\mathrm{Spec}\,\rho$.
--
--   This is the classifying half of Raynaud's description of the identity component of the Néron model, in the shape consumed by the level-$p$ crossing analysis: an invertible sheaf on the model over the valuation ring with prescribed generic fibre and trivial restriction to both components of the special fibre produces an $A$-valued point of the relative $\mathrm{Pic}^0$ scheme extending the given divisor class. It is used by [`ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter`](thm.html#ModularCurve.XHDRModelAtP.extendsToPlace_pts_mk_smul_single_sub_single_of_range_subset_range_comp_inter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_extendsToPlace_pts_pic0Mk_single_sub_single_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
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
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.extendsToPlace_pts_pic0Mk_single_sub_single_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
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
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (ψ : SchemeHomOver (genPt p) (Spec.map (CommRingCat.ofHom ρ))) (hψ : ψ.1 = barPt A)
    (β : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (Spec.map (CommRingCat.ofHom ρ)))
    (hβ : β.1 = resPt A)

    (y₁ y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (ybar₁ ybar₂ : SchemeHomOver (genPt p) (toBase p (ΓM M H) hj))
    (hybar₁ : ybar₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hybar₂ : ybar₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p))

    (L : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Modules)
    (hL : Scheme.Modules.IsInvertible L)
    (hgen : Nonempty ((Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓM M H) hj) ψ)).obj L ≅
      (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₁.1 ybar₁.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) ybar₂.1 ybar₂.2).idealModule))
    (hcomp : ∀ i : Fin 2, Nonempty ((Scheme.Modules.pullback (𝔛.comp A hA ρ hρ i ≫ baseChangeSnd (toBase p (ΓM M H) hj) β)).obj L ≅
      𝟙_ (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)).Modules))
    (hdeg : Finsupp.single (𝔛.Meta.pointEquivPlace y₁) (1 : ℤ) - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1
      ∈ Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))) :
    ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ))
      (pts (Pic0.mk ⟨Finsupp.single (𝔛.Meta.pointEquivPlace y₁) (1 : ℤ) - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1, hdeg⟩)) := by sorry
