-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/9225ec8b-cdd9-573a-9662-bad02a0ca1d7
-- title:
--   An A-point of Pic⁰ classifying a given line bundle
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, the hypothesis `hj` that `jqModC ℚ` lies in `qExpFunctionFieldC ℚ ⊤`, and a term $\mathfrak{X}$ of `XHDRModelAtP p M H hpM hj`; thus the curve `X p (ΓM M H) hj` over `Spec (R p)`, with structure morphism `toBase p (ΓM M H) hj`, assumed proper, comes with a section `𝔛.εinf` over `Spec (R p)`, with a `CurveModel` `𝔛.Meta` over $\overline{\mathbb{Q}}$ whose function field is `xHFunctionFieldBar M H` and whose closed points correspond to places via `𝔛.Meta.pointEquivPlace`, and with an isomorphism `𝔛.eeta` from `𝔛.Meta.C` onto the geometric generic fibre. Let `D` consist of a scheme `D.P` over `Spec (R p)` with a zero section, and let `hD`, respectively `hDQ`, assert that `D`, respectively `D.baseChange ℚ`, represents the functor of line bundles rigidified along `𝔛.εinf` (respectively `sectionBaseChange ℚ 𝔛.εinf`) satisfying the fibrewise algebraic-equivalence-to-zero condition `algEquivZeroCut`, with Poincaré bundles `hD.poincare`, `hDQ.poincare`; `hPQ` identifies `hDQ.poincare.L` with the base change to ℚ of the pullback of `hD.poincare` along `pullback.fst D.toBase (specMap (R p) ℚ)`. Further data: an Abel–Jacobi morphism `ajQ` from the ℚ-fibre of the curve to `(D.baseChange ℚ).toBase` carrying the cusp section to the zero section (`hajQε`) and satisfying, for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every $K$-point $x$ of the ℚ-fibre, an isomorphism between the pullback of `hDQ.poincare` along $x$ followed by `ajQ.1` and `(RelEffCartierDiv.ofPoint … x).lineBundle` tensored with the ideal module of the divisor cut out by the cusp at $t$ (`hajQ`); a comparison morphism `kQ` of the geometric generic fibre with the ℚ-fibre compatible with both projections; the composite `ajbar` of `𝔛.eeta`, `kQ`, `ajQ.1` and `pullback.fst D.toBase (specMap (R p) ℚ)`, a morphism `𝔛.Meta.C ⟶ D.P` over `genPt p`; a $\overline{\mathbb{Q}}$-point `εbar` of `𝔛.Meta.C` lying over the cusp and sent by `ajbar` to the zero section; and a bijection `pts` from `JH M H`, the degree-zero divisor class group of `xHFunctionFieldBar M H`, to the $\overline{\mathbb{Q}}$-points of `D.toBase`, additive for the relative group law attached to `hD`, Galois-equivariant, and compatible with `ajbar` in the sense that for all $\overline{\mathbb{Q}}$-points $x, s$ of `𝔛.Meta.C` with $s$ over the cusp there is a degree-zero divisor equal to $[\text{place of } x] - [\text{place of } s]$ whose image under `pts ∘ Pic0.mk` is $x$ followed by `ajbar`. Finally let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, residue field algebraically closed of characteristic $p$, let $\rho :$ `R p` $\to A$ be a ring map compatible with `algebraMap (R p) (AlgebraicClosure ℚ)`, and let `ψ`, `β` be the morphisms `barPt A` and `resPt A` viewed over `Spec.map ρ`. Given $\overline{\mathbb{Q}}$-points $y_1, y_2$ of `𝔛.Meta.C`, with associated points `ybar₁`, `ybar₂` of the curve over `genPt p`, and given a module $L$ on `pullback (toBase p (ΓM M H) hj) (Spec.map ρ)` that is invertible (`hL`), whose pullback along `baseChangeSnd … ψ` is isomorphic to `(RelEffCartierDiv.ofPoint … ybar₁).lineBundle ⊗ (RelEffCartierDiv.ofPoint … ybar₂).idealModule` (`hgen`), and whose pullback along each of the two morphisms `𝔛.comp A hA ρ hρ i ≫ baseChangeSnd … β`, $i \in \{0,1\}$, is isomorphic to the unit module on the fibre of `toBase p (ΓN p M H hpM) hj` over the residue field of $A$ (`hcomp`), and assuming the divisor $[\text{place of } y_1] - [\text{place of } y_2]$ has degree zero (`hdeg`): there exists a morphism $a$ from `Spec A` to `D.P` over `Spec.map ρ` such that the point `pts` of the class of that divisor equals `barPt A` followed by $a$, and the pullback of `hD.poincare` along $a$ has underlying module isomorphic to $L$.
--
--   This is the specialisation step for the relative Picard functor of the Deligne–Rapoport model of $X_H(M)$ at a prime exactly dividing the level: a line bundle on the model over a valuation ring $A$ above $p$ that restricts to $\mathcal{O}(y_1 - y_2)$ on the geometric generic fibre and is trivial on both components of the special fibre is classified by an $A$-valued point of the representing object $D$, extending the $\overline{\mathbb{Q}}$-point $\mathrm{pts}([y_1]-[y_2])$. It is used in the construction of the Néron-type object attached to $J_H$ at $p$, in the analysis of the action of inertia at $p$ on points of the Jacobian that underlies level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit.lean

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

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_pts_pic0Mk_eq_barPt_comp_and_poincare_pullbackAlong_iso_of_isInvertible_of_iso_ofPoint_tensor_idealModule_of_iso_tensorUnit
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
    ∃ a : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      (pts (Pic0.mk ⟨Finsupp.single (𝔛.Meta.pointEquivPlace y₁) (1 : ℤ) - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1, hdeg⟩)).1 =
          barPt A ≫ a.1 ∧
        Nonempty ((hD.poincare.pullbackAlong a).L ≅ L) := by sorry
