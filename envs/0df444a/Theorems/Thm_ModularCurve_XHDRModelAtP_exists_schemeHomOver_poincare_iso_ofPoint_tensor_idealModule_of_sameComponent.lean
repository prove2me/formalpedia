-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent
-- name    : ModularCurve.XHDRModelAtP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/e768b6f4-02ed-5130-bb8f-69a0b599bace
-- title:
--   An A-point of relative Pic⁰ carrying 𝒪(u₁)⊗𝒪(u₂)⁻¹
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H\le(\mathbb Z/M)^{\times}$, and the hypothesis that the $q$-expansion $jqModC$ of $j$ lies in the function field $qExpFunctionFieldC\,\mathbb Q\,\mathrm{SL}_2(\mathbb Z)$, so that the two-chart integral model $X$ of $X_H(M)$ over $R\,p$ with structure morphism `toBase` is available; let $\mathfrak X$ be a `XHDRModelAtP` datum for these, and assume `toBase` separated. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R\,p \to A$ compatible with $R\,p \to \overline{\mathbb Q}$. Let $D$ be a relative $\mathrm{Pic}^0$ designation for `toBase` (a scheme over $\operatorname{Spec}(R\,p)$ with a zero section) and $hD$ a datum representing, via the cut `algEquivZeroCut` of fibrewise algebraically-trivial rigidified line bundles at $\mathfrak X.\varepsilon_{\inf}$, the corresponding subfunctor of rigidified bundles on $X$, with Poincaré bundle $hD.poincare$. Give $\kappa$ the $R\,p$-algebra structure induced by $\rho$ followed by the residue map. Then, for every representing datum $hD\kappa$ for the base change of the situation to $\kappa$ (with section $sectionBaseChange$ and designation $D.baseChange\,\kappa$), every isomorphism between its Poincaré bundle and the bundle obtained from $hD.poincare$ by pulling back along the first projection of $D.toBase \times_{\operatorname{Spec}(R\,p)} \operatorname{Spec}\kappa$ and transporting by `BaseChange.ofR`, every $i \in \{0,1\}$, and every pair of $A$-points $u_1,u_2$ of $X$ over $\operatorname{Spec}\rho$ whose images lie in $\mathfrak X.smoothLocus$, together with $\kappa$-sections $u_{\kappa,1},u_{\kappa,2}$ of the fibre $X\times_{R\,p}\kappa$ reducing $u_1,u_2$ and having closed point in the image of $\mathfrak X.comp\,A\,hA\,\rho\,h\rho\,i$ for the same $i$: there exists an $A$-point $s$ of $D.toBase$ such that the pullback of $hD.poincare$ along $s$ is isomorphic to $\mathcal O(u_1)\otimes\mathcal O(u_2)^{-1}$, meaning the dual (`invModule`) of the ideal sheaf of the graph divisor `RelEffCartierDiv.ofPoint` of $u_1$ tensored with the ideal sheaf (`idealModule`) of that of $u_2$, and moreover every $\kappa$-point $y$ of $(D.baseChange\,\kappa).toBase$ over the identity of $\operatorname{Spec}\kappa$ whose first projection is $s$ composed after $\operatorname{Spec}\kappa\to\operatorname{Spec}A$ satisfies that the pullback of $hD\kappa.poincare$ along $y$ is isomorphic to the analogous tensor product formed from $u_{\kappa,1}$ and $u_{\kappa,2}$ on the base change of $X$ to $\kappa$.
--
--   This is the divisor-class dictionary for the Deligne–Rapoport model at a prime exactly dividing the level: a difference of two sections landing on one component of the special fibre defines a point of the relative $\mathrm{Pic}^0$ scheme over the valuation ring, compatibly with reduction. It is used in the description of the special fibre of the group of points and in the statements that classes of differences of cusps or points extend to places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D) :
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔛.εinf))
        (D.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (huκ₁ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (_ : uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base)
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (huκ₂ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (_ : uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base),
    ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong s).L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
      ∀ (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase),
        y.1 ≫ pullback.fst _ _ = resPt A ≫ s.1 →
        Nonempty ((hDκ.poincare.pullbackAlong y).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) uκ₁ huκ₁).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) uκ₂ huκ₂).idealModule) := by sorry
