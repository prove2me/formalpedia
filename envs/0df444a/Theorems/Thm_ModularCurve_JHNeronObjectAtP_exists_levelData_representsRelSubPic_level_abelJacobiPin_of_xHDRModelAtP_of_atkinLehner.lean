-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_levelData_representsRelSubPic_level_abelJacobiPin_of_xHDRModelAtP_of_atkinLehner
-- name    : ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_level_abelJacobiPin_of_xHDRModelAtP_of_atkinLehner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/6e187328-8311-51cc-87d7-7f2a53b7ffc9
-- title:
--   Abel–Jacobi-pinned Néron object for J_H(M) at p ∥ M
-- statement:
--   Fix a prime $p$ and $M\ge 1$ with $p\mid M$ and $p^2\nmid M$, a subgroup $H\le(\mathbb Z/M)^\times$ containing the kernel of reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$, with $M/p\neq 0$, and assume the $q$-expansion `jqModC ℚ` of $j$ lies in the $q$-expansion function field of level $SL(2,\mathbb Z)$. Let $\mathfrak X$ be a model of type `XHDRModelAtP p M H hpM hj` for $X_H(M)$ over the base ring `R p`; let $\theta$ be an $\overline{\mathbb Q}$-algebra automorphism of `xHFunctionFieldBar M H` which, on elements whose Laurent series come from level $M/p$, acts by the substitution $q\mapsto q^{p}$ (`qExpand`), and assume that any two $\overline{\mathbb Q}$-points of $\mathfrak X.\mathrm{Meta}.C$ over the base related by composition with the isomorphism `𝔛.w` have places related by the semilinear automorphism `SemilinearAut.ofAlgAut θ`. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$, and $\rho\colon$ `R p` $\to A$ a ring homomorphism compatible with the structural map `R p` $\to\overline{\mathbb Q}$. Then there exist: a level datum $\Lambda$ (a morphism $\sigma_A\colon \operatorname{Spec}A\to$ `base p` lifting the geometric generic point, a scheme $X$ over `base p` with a relative group law and a bijection of $J_H(M/p)=\mathrm{Pic}^0$ of `xHFunctionFieldBar (M/p) (infSubgroup …)` with its generic-fibre points, together with a special-fibre parametrisation); a record $O$ of type `JHNeronObjectAtP p M H hpM A hA Λ` (a smooth, separated, surjective group scheme $g\colon G\to$ `base p` with connected fibres, a relative group law, a bijection `O.pts` of $J_H(M)=\mathrm{Pic}^0$ of `xHFunctionFieldBar M H` with its $\overline{\mathbb Q}$-points, Galois equivariance and Hecke endomorphisms); data $h_D$ exhibiting $(G,g)$ with the unit section as a relative $\mathrm{Pic}^0$-designation representing, over `R p`, the rigidified line bundles on $\mathfrak X$ at level $\Gamma_M$ that are fibrewise algebraically equivalent to zero, rigidified along $\mathfrak X.\varepsilon_\infty$, together with its analogue $h_{D\mathbb Q}$ after base change to $\mathbb Q$ and separatedness of that base change; a morphism $aj_{\mathbb Q}$ from the generic-fibre curve to the base-changed designation; a comparison morphism $k_{\mathbb Q}$ between the $\overline{\mathbb Q}$- and $\mathbb Q$-fibres; a morphism $\overline{aj}\colon\mathfrak X.\mathrm{Meta}.C\to G$; and a $\overline{\mathbb Q}$-point $\bar\varepsilon$ of $\mathfrak X.\mathrm{Meta}.C$ over the base. These satisfy: $\Lambda.\sigma_A=\operatorname{Spec}\rho$; the analogous representability of $(\Lambda.X,\Lambda.f)$ with unit section for the level-$\Gamma_N$ model rigidified along $\varepsilon_\infty$ followed by $\mathfrak X.\pi$; an isomorphism of the Poincaré bundle of $h_{D\mathbb Q}$ with the base change to $\mathbb Q$ of that of $h_D$; $\varepsilon_\infty\circ$-composed with $aj_{\mathbb Q}$ equals the zero section; for every field $K$, every $t\colon\operatorname{Spec}K\to\operatorname{Spec}\mathbb Q$ and every $K$-point $x$ of the generic-fibre curve, the pullback of the Poincaré bundle along $x$ followed by $aj_{\mathbb Q}$ is isomorphic to the line bundle of the relative effective Cartier divisor of $x$ tensored with the ideal module of that of $t$ followed by the base-changed $\varepsilon_\infty$; the two compatibilities identifying $k_{\mathbb Q}$ as the canonical comparison over $\mathbb Q\subset\overline{\mathbb Q}$; $\overline{aj}=\mathfrak X.\mathrm{eeta}$ followed by $k_{\mathbb Q}$, $aj_{\mathbb Q}$ and the first projection, with $\overline{aj}$ lying over the geometric generic point; $\bar\varepsilon$ lying over $\varepsilon_\infty$ and mapping under $\overline{aj}$ to the unit; additivity of `O.pts` for the group law induced by $h_D$ through the sub-Picard group condition; and, for all $\overline{\mathbb Q}$-points $x,s$ of $\mathfrak X.\mathrm{Meta}.C$ with $s$ lying over $\varepsilon_\infty$, existence of a degree-zero divisor equal to $[\,x\,]-[\,s\,]$ on the places attached to $x$ and $s$ whose class has `O.pts`-image given by $x$ followed by $\overline{aj}$.
--
--   This is the existence statement for the Néron-model-of-record at a prime exactly dividing the level, realised as the relative $\mathrm{Pic}^0$ of a Deligne–Rapoport model of $X_H(M)$ over $\mathbb Z_{(p)}$, with the Abel–Jacobi morphism normalised at the cusp $\infty$ so that the divisor class $[x]-[s]$ corresponds to the point $x$ of the Jacobian. It is the input to the lemmas describing the action of inertia at $p$ on toric points, which feed the level-lowering step of the Frey–Serre–Ribet argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_levelData_representsRelSubPic_level_abelJacobiPin_of_xHDRModelAtP_of_atkinLehner.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

set_option maxHeartbeats 400000 in

theorem ModularCurve.JHNeronObjectAtP.exists_levelData_representsRelSubPic_level_abelJacobiPin_of_xHDRModelAtP_of_atkinLehner
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∃ (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

      (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

      (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
      (_ : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
      (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
      (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
      (ajbar : 𝔛.Meta.C ⟶ O.G)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),

      Λ.σA = Spec.map (CommRingCat.ofHom ρ) ∧

      Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))) ∧

      Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L) ∧

      (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection ∧

      (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
                (Category.comp_id t)))).idealModule)) ∧

      kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p) ∧
      kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ) ∧

      ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ) ∧
      ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p ∧
      εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 ∧
      εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1 ∧

      (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)) ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
          (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
            Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
          (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar) := by sorry
