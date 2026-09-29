-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi
-- name    : ModularCurve.JHNeronObjectAtP.baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/188b91a0-9854-5234-9cd9-212465cc376a
-- title:
--   Points over A: θ-twist equals composition with N
-- statement:
--   Fix a prime $p$ and a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and divisibility data $hpM : p \mid M$ together with $hpM2 : p^{2} \nmid M$; the hypothesis $hHp$ requires that every unit of $\mathbb{Z}/M$ whose image under `ZMod.unitsMap` for the divisor $M/p$ is trivial already lies in $H$. The hypothesis $hj$ asserts that the $q$-expansion $j(q)$, as an element of `LaurentSeries ℚ`, lies in the intermediate field $\mathrm{qExpFunctionFieldC}\ \mathbb{Q}\ \mathrm{SL}(2,\mathbb{Z})$, so that the two-chart integral model $\mathfrak{X}$-base `toBase p (ΓM M H) hj` over `R p` is available; $\mathfrak{X}$ is a Deligne–Rapoport-type datum of type `XHDRModelAtP p M H hpM hj`, which in particular supplies a curve model `𝔛.Meta` of the function field `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$, the comparison isomorphism `𝔛.eeta` onto the $\overline{\mathbb{Q}}$-fibre of the integral model, and the section `𝔛.εinf` at infinity. Further, $A$ is a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with $hA : p$ a non-unit of $A$, whose residue field is of characteristic $p$ and algebraically closed, $\Lambda$ is level data of type `JHNeronObjectAtP.LevelData p M H hpM A`, and $O$ is a `JHNeronObjectAtP p M H hpM A hA Λ`: a smooth separated group object $O.G \to$ `base p` with relative group law $O.L$ and a bijection $O.\mathrm{pts}$ from $J_H(M) =$ `JH M H`, the degree-zero divisor classes of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ modulo principal divisors, onto the points of $O.g$ over `genPt p`. Throughout, $D$ denotes the relative $\mathrm{Pic}^{0}$ designation over `R p` consisting of the scheme $O.G$, the structure morphism $O.g$ and the zero section given by the identity point of $O.L$ at the identity of $\operatorname{Spec}$ `R p`.
--
--   Representability over `R p`: the hypothesis $hD$ asserts that $D$ represents the relative sub-Picard functor of the curve `toBase p (ΓM M H) hj` rigidified along `𝔛.εinf` and cut out by `algEquivZeroCut`, that is, by fibrewise algebraic equivalence to zero — so there is a Poincaré rigidified line bundle satisfying the condition, every rigidified line bundle satisfying it over a base $T$ is classified by a unique $T$-point up to isomorphism, and the zero section classifies the unit bundle. The hypothesis $hL$ identifies the law $O.L$ with the relative group law `RepresentsRelSubPic.relativeGroupLaw` obtained from $hD$ for the group cut `algEquivZeroGroupCut`.
--
--   Representability and comparison over $A$: $A$ is an `R p`-algebra; $hDA$ asserts that the base change of $D$ to $A$ represents the corresponding cut for the base-changed curve with the base-changed section `sectionBaseChange ↥A 𝔛.εinf`; $hpoincA$ asserts that the Poincaré bundle of $hDA$ is isomorphic to the bundle obtained by `BaseChange.ofR` from the pullback of the Poincaré bundle of $hD$ along the first projection of the pullback of $O.g$ and `specMap (R p) ↥A`; $hLA$ asserts that for every base $t' : T \to \operatorname{Spec} A$ and all points $x,y$ over $t'$ the multiplication supplied by $hDA$ agrees with the base change along `specMap (R p) ↥A` of the multiplication supplied by $hD$. The morphism $kA$ goes from the $\overline{\mathbb{Q}}$-fibre of the integral model to its $A$-fibre, with $hkA_1$ and $hkA_2$ asserting compatibility with the two projections, the second up to composition with `barPt A`.
--
--   Data over $\mathbb{Q}$ and the Abel–Jacobi pinning: $hDQ$ is the representability statement for the base change of $D$ to $\mathbb{Q}$ against the $\mathbb{Q}$-base-changed curve and section, $hsepQ$ asserts that the $\mathbb{Q}$-base-changed curve is separated, $ajQ$ is a point of the base of $D \otimes \mathbb{Q}$ over the $\mathbb{Q}$-curve, $kQ$ is a morphism from the $\overline{\mathbb{Q}}$-fibre to the $\mathbb{Q}$-fibre of the integral model, $hpoinc$ ties the Poincaré bundle of $hDQ$ to the `BaseChange.ofR` transport of the pullback of the Poincaré bundle of $hD$ along the first projection over $\mathbb{Q}$, $hajε$ asserts that the section at infinity followed by $ajQ$ is the zero section of $D \otimes \mathbb{Q}$, and $hajcl$ asserts the Abel–Jacobi bundle identity: for every field $K$, every $t : \operatorname{Spec} K \to \operatorname{Spec}\mathbb{Q}$ and every point $x$ of the $\mathbb{Q}$-curve over $t$, the pullback of the Poincaré bundle of $hDQ$ along $x$ followed by $ajQ$ is isomorphic to the tensor product of the line bundle of the relative effective Cartier divisor of the point $x$ with the ideal module of the relative effective Cartier divisor of the section $t$ followed by `sectionBaseChange ℚ 𝔛.εinf`. The hypotheses $hkQ_1$ and $hkQ_2$ assert compatibility of $kQ$ with the two projections, the second up to composition with `specMap ℚ (AlgebraicClosure ℚ)`.
--
--   The morphism $ajbar : \mathfrak{X}.\mathrm{Meta}.C \to O.G$ and the $\overline{\mathbb{Q}}$-point $\bar\varepsilon$ of $\mathfrak{X}.\mathrm{Meta}.C$ over its base are pinned as follows: $hajbar$ states that $ajbar$ is `𝔛.eeta` followed by $kQ$, by $ajQ$, and by the first projection of the pullback of $O.g$ and `specMap (R p) ℚ`; $hajbar\_over$ states that $ajbar$ followed by $O.g$ equals `𝔛.Meta.toBase` followed by `genPt p`; $h\bar\varepsilon$ states that $\bar\varepsilon$ followed by `𝔛.eeta` and the first projection equals `genPt p` followed by the section at infinity; $h\bar\varepsilon\_aj$ states that $\bar\varepsilon$ followed by $ajbar$ equals `genPt p` followed by the identity point of $O.L$. The hypothesis $hpts\_law$ asserts that $O.\mathrm{pts}$ is additive for the group law coming from $hD$, and $hAJ$ asserts that for all $\overline{\mathbb{Q}}$-points $x,s$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base such that $s$ satisfies the pinning condition at infinity, there is a degree-zero divisor $Dv$ of `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ equal to $\mathrm{single}(\mathrm{place}(x),1) - \mathrm{single}(\mathrm{place}(s),1)$, where places are taken through `𝔛.Meta.pointEquivPlace`, whose class satisfies $(O.\mathrm{pts}([Dv])).1 = x$ followed by $ajbar$.
--
--   The automorphism data: $\varphi$ is a self-isomorphism of the $A$-fibre of the integral model, with $h\varphi$ asserting that $\varphi$ is an automorphism over $\operatorname{Spec} A$, and $\theta$ is a $\overline{\mathbb{Q}}$-algebra automorphism of `xHFunctionFieldBar M H`; the hypothesis $h\varphi\theta$ asserts that for all $\overline{\mathbb{Q}}$-points $y,y'$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, if $y'$ followed by `𝔛.eeta`, $kA$ and $\varphi$ equals $y$ followed by `𝔛.eeta` and $kA$, then the place of $y'$ is the translate of the place of $y$ by `SemilinearAut.ofAlgAut θ`. The hypothesis $hbar$ states that `genPt p` factors as `barPt A` followed by `specMap (R p) ↥A`.
--
--   Finally, $N$ is an endomorphism over $\operatorname{Spec} A$ of the base of the $A$-base change of $D$, subject to three clauses: $hN_1$ asserts that for every $t : T \to \operatorname{Spec} A$ and every point $a$ over $t$, the pullback of the Poincaré bundle of $hDA$ along $a$ followed by $N$ is isomorphic to the `Scheme.Modules.rigidify` along `rigSection` and the second projection of the pullback along `curveChange φ.hom hφ t` of the pullback of that Poincaré bundle along $a$; $hN_2$ asserts that $N$ is compatible with the multiplication supplied by $hDA$; and $hN_3$ asserts that the zero section of the $A$-base change of $D$ followed by $N$ is again that zero section.
--
--   Under these hypotheses the conclusion is: for every $x \in J_H(M)$, the underlying morphism of the point over $\operatorname{Spec} A$ obtained by `RelativeGroupLaw.baseChangePointOfBase` along `specMap (R p) ↥A` from the point $O.\mathrm{pts}(\mathrm{ofAlgAut}(\theta) \cdot x)$, recast along $hbar$ as a point over `barPt A` followed by `specMap (R p) ↥A`, equals the underlying morphism of the point obtained in the same way from $O.\mathrm{pts}(x)$, followed by $N$.
--
--   This is the compatibility, over the valuation subring $A$, between the Galois/automorphism action on degree-zero divisor classes of the function field of $X_H$ and the endomorphism $N$ of the $A$-model of the Jacobian classifying pullback of rigidified line bundles along the automorphism $\varphi$ of the integral curve over $A$; the corresponding statement over the base ring `R p` is its arithmetic counterpart. It feeds the construction of automorphisms of the $A$-model extending a given automorphism of the curve, and is cited by [`ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_of_baseChangeModelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_baseChange_abelJacobi`](thm.html#ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_of_baseChangeModelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_baseChange_abelJacobi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi.lean

import Mathlib
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
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.baseChangePointOfBase_pts_ofAlgAut_smul_eq_comp_of_classifies_rigidify_pullback_curveChange_baseChange_of_abelJacobi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hL : O.L = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD)

    [Algebra (R p) ↥A]
    (hDA : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A))
    (hpoincA : Nonempty (hDA.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ↥A
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ↥A), pullback.condition⟩)).L))

    (hLA : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t' ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t' x y =
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD).baseChange (specMap (R p) ↥A)).mul t' x y)
    (kA : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hkA₁ : kA ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkA₂ : kA ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ↥A) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ barPt A)
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsepQ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})

    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))

    (hajε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)

    (hajcl : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule))

    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)

    (hpts_law : ∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y))
    (hAJ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (φ : pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A) ≅ pullback (toBase p (ΓM M H) hj) (specMap (R p) ↥A))
    (hφ : φ.hom ≫ baseChange (R p) (toBase p (ΓM M H) hj) ↥A = baseChange (R p) (toBase p (ΓM M H) hj) ↥A)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ kA ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ kA →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hbar : genPt p = barPt A ≫ specMap (R p) ↥A)

    (N : SchemeHomOver ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase)
    (hN₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A)) (a : SchemeHomOver t ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        Nonempty ((hDA.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) t (sectionBaseChange ↥A 𝔛.εinf)) (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) t)
            ((Scheme.Modules.pullback (curveChange φ.hom hφ t)).obj (hDA.poincare.pullbackAlong a).L)))
    (hN₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥A)) (x y : SchemeHomOver t ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (baseChange (R p) (toBase p (ΓM M H) hj) ↥A) (sectionBaseChange ↥A 𝔛.εinf)) hDA).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N))
    (hN₃ : ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).zeroSection ≫ N.1 = ((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)).baseChange ↥A).zeroSection) :
    ∀ x : JH M H,
      (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts (SemilinearAut.ofAlgAut θ • x)))).1 =
        (RelativeGroupLaw.baseChangePointOfBase (specMap (R p) ↥A) (castOver hbar (O.pts x))).1 ≫ N.1 := by sorry
