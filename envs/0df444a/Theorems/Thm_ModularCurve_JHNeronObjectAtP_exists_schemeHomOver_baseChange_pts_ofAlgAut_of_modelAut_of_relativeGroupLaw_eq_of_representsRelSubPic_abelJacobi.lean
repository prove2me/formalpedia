-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_ofAlgAut_of_modelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_abelJacobi
-- name    : ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_of_modelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_abelJacobi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/24972c6d-3675-5a8e-b4d4-74a74a04ce45
-- title:
--   Model automorphism gives a homomorphic endomorphism over A
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial; assume the $q$-expansion $j$ lies in the level-one $q$-expansion function field over $\mathbb{Q}$ (`hj`), and let $\mathfrak{X}$ be a Deligne–Rapoport-type model datum `XHDRModelAtP` for $X_H(M)$ over $R_p$, with curve `toBase p (ΓM M H) hj`, cusp section $\varepsilon_\infty$, geometric curve model $\mathfrak{X}.\mathrm{Meta}$ of $\overline{\mathbb{Q}}\cdot F(X_H(M))$ and comparison isomorphism `eeta`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits and algebraically closed residue field of characteristic $p$, $\Lambda$ level data (in particular a structure morphism $\sigma_A$ with $\mathrm{barPt}\,A \circ \sigma_A$ the generic point), and $O$ a `JHNeronObjectAtP`: a smooth separated group object $g \colon G \to \mathrm{base}\,p$ with relative group law $O.L$ and bijection $O.\mathrm{pts} \colon J_H(M) = \mathrm{Pic}^0(\overline{\mathbb{Q}}\cdot F(X_H(M))) \simeq$ sections of $g$ over the generic point. The hypotheses assert: $(G,g,\text{unit section})$ represents, as a relative $\mathrm{Pic}^0$ designation, the subfunctor of rigidified line bundles on the model that are fibrewise algebraically equivalent to zero (`hD`), with $O.L$ the group law transported through that representability (`hL`); the analogous representability after base change to $\mathbb{Q}$ (`hDQ`), separatedness of the base-changed curve (`hsepQ`), an Abel–Jacobi morphism $\mathrm{aj}_\mathbb{Q}$ over $\mathbb{Q}$ together with a comparison morphism $k_\mathbb{Q}$ of pullbacks, a morphism $\overline{\mathrm{aj}}\colon \mathfrak{X}.\mathrm{Meta}.C \to G$ and a $\overline{\mathbb{Q}}$-point $\overline{\varepsilon}$; an isomorphism of the Poincaré bundle over $\mathbb{Q}$ with the base change of that over $R_p$ (`hpoinc`); pins stating that $\mathrm{aj}_\mathbb{Q}$ carries the cusp to the zero section and classifies, for every field $K$ and $K$-point $x$, the bundle $\mathcal{O}(x) \otimes \mathcal{I}(\varepsilon_\infty)$ (`hajcl`); the compatibilities of $k_\mathbb{Q}$, of $\overline{\mathrm{aj}}$ with $g$ and with $\overline{\varepsilon}$; additivity of $O.\mathrm{pts}$ for the transported law; and an Abel–Jacobi dictionary: for $\overline{\mathbb{Q}}$-points $x$ and a cusp point $s$ there is a degree-zero divisor equal to $[\,\text{place of } x\,] - [\,\text{place of } s\,]$ whose class is sent by $O.\mathrm{pts}$ to $x \circ \overline{\mathrm{aj}}$. Finally let $\varphi$ be an automorphism of the model curve over $\mathrm{Spec}\,R_p$ and $\theta$ an $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{\mathbb{Q}}\cdot F(X_H(M))$ such that whenever $y'$ followed by `eeta` and the first projection and then $\varphi$ equals the corresponding composite for $y$, the place of $y'$ is $\theta$ (viewed as a semilinear automorphism) applied to the place of $y$. The conclusion: there exists an endomorphism $W$ of the base change $G \times_{R_p} A$ over $\mathrm{Spec}\,A$ which (i) is a homomorphism for the base-changed group law, i.e. for all $T$, $s \colon T \to \mathrm{Spec}\,A$ and sections $x,y$, composing the product with $W$ equals the product of $x \circ W$ and $y \circ W$, and (ii) satisfies $O.\mathrm{pts}(\theta \cdot x) =$ the generic-point section obtained from lifting $O.\mathrm{pts}(x)$ to an $A$-point of the base change and composing with $W$, for every $x \in J_H(M)$.
--
--   This transports an automorphism carried by the integral model of $X_H(M)$ (such as a Fricke or Atkin–Lehner involution) to an endomorphism of the Néron object over the place $A$, homomorphic for the group law and matching, on points, the induced action $\theta$ on degree-zero divisor classes; the mechanism is functoriality of the rigidified relative Picard functor combined with the Abel–Jacobi pins. It feeds the Atkin–Lehner/Fricke complement statement at this level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_schemeHomOver_baseChange_pts_ofAlgAut_of_modelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_abelJacobi.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_baseChange_pts_ofAlgAut_of_modelAut_of_relativeGroupLaw_eq_of_representsRelSubPic_abelJacobi
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hL : O.L = RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut (toBase p (ΓM M H) hj) 𝔛.εinf) hD)
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

    (φ : X p (ΓM M H) hj ≅ X p (ΓM M H) hj) (hφ : φ.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))

    (hφθ : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ φ.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y) :
    ∃ W : SchemeHomOver (RelativeGroupLaw.baseChangeStr Λ.σA O.g) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥A))
          (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr Λ.σA O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange Λ.σA).mul s x y) W =
          (O.L.baseChange Λ.σA).mul s (NeronModelInfra.schemeHomOverComp x W) (NeronModelInfra.schemeHomOverComp y W)) ∧
      (∀ x : JH M H, O.pts (SemilinearAut.ofAlgAut θ • x) =
        genOfBaseChangePt Λ.hσA (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase Λ.σA (castOver Λ.hσA.symm (O.pts x))) W)) := by sorry
