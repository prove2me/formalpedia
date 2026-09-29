-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth
-- name    : ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/23fe96b2-ba8e-54db-9424-dab51359524f
-- title:
--   Two-line degeneration of a non-smooth Deligne–Rapoport fibre
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a term of `DRModelPackage p`, i.e. the two-chart integral model `DRModel p` of the full modular function field over $\operatorname{Spec}\mathbf Z$ together with properness, flatness, integrality and normality data, curve models of its fibres over $\mathbf Q$ and over $\overline{\mathbf Q}$ with their Galois compatibilities, two sections $\varepsilon_\infty,\varepsilon_0$ over $\operatorname{Spec}\mathbf Z$, and a maximal open subscheme `smoothLocus` smooth of relative dimension $1$ over the base. The assertion is: for every algebraically closed field $k$ and every $s:\operatorname{Spec}k\to\operatorname{Spec}\mathbf Z$ such that the projection $\mathfrak X_s:=$ `pullback (DRModel.toBase p) s` $\to\operatorname{Spec}k$ is not smooth, there are two objects $M_1,M_2$ of `CurveModel k (RatFunc k)` — integral schemes proper and smooth of relative dimension $1$ over $k$, with function field identified with $k(t)$ as $k$-algebra and with a bijection `placeEquiv` from their closed points to the places of $k(t)$ over $k$ matching stalks with valuation subrings, every finite set of points lying in an affine open — together with closed immersions $i_1:M_1\to\mathfrak X_s$, $i_2:M_2\to\mathfrak X_s$, an $n\in\mathbf N$, families $a,b:\mathrm{Fin}\,n\to k^\times$ and a cover $\mathcal W_0$ of $\mathfrak X_s$ by two affine opens $U_0,U_1$ with $U_0\sqcup U_1=\top$ and affine intersection, such that: $i_j$ followed by the projection to $\operatorname{Spec}k$ is $M_j$'s structure morphism ($j=1,2$); the images of $i_1$ and $i_2$ on points cover $\mathfrak X_s$; $a$ is injective; for each $i$ the point $t=a_i$ of $M_1$ and the point $t=b_i$ of $M_2$ (the closed points corresponding under `placeEquiv` to `placeOfPoint`) have the same image, and conversely any pair $(P_1,Q_2)$ with $i_1(P_1)=i_2(Q_2)$ is of this form for some $i$; the scheme-theoretic fibre product `pullback i₁ i₂` is reduced; $i_j^{-1}U_0$ is the complement of the point at infinity of $M_j$ and $i_j^{-1}U_1$ the complement of the point $t=0$, for $j=1,2$; $i_1$ sends the point at infinity of $M_1$ to the image of the closed point of $\operatorname{Spec}k$ under `sectionFibrePoint 𝔛.εinf s`, the lift of $s$ followed by $\varepsilon_\infty$ to $\mathfrak X_s$; the image of $i_1$ meets the preimage of `𝔛.smoothLocus` under the first projection exactly in the connected component of that $\varepsilon_\infty$-point inside that preimage; none of the points $i_1(t=a_i)$ lies in this preimage, while every point of $\mathfrak X_s$ distinct from all of them does; and there is an open $W_1\subseteq\mathfrak X_s$ whose underlying set is the complement of the image of $i_2$, such that the inclusion of $i_1^{-1}W_1$ into $M_1$ followed by $i_1$ is an open immersion.
--
--   This is the Deligne–Rapoport description of the bad fibre of $X_0(p)$ — two copies of the $j$-line meeting transversally at the supersingular points — recast as the "two-line degeneration" data attached to a non-smooth geometric fibre of the integral model, with the $\varepsilon_\infty$-section singling out one of the two components. It supplies the degeneration hypothesis for the representability of the relative $\operatorname{Pic}^0$ of the model, and is cited by [`ModularCurve.nonempty_legTwoInputV2`](thm.html#ModularCurve.nonempty_legTwoInputV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_ModularCurve_DRModelLegTwoInputV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)), ¬ Smooth (pullback.snd (DRModel.toBase p) s) →
    ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback (DRModel.toBase p) s) (i₂ : M₂.C ⟶ pullback (DRModel.toBase p) s)
      (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
      (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback (DRModel.toBase p) s).TwoAffineOpenCover),
      i₁ ≫ pullback.snd (DRModel.toBase p) s = M₁.toBase ∧ i₂ ≫ pullback.snd (DRModel.toBase p) s = M₂.toBase ∧
      Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
      Function.Injective a ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (P₁ : M₁.C) (Q₂ : M₂.C), i₁.base P₁ = i₂.base Q₂ →
        ∃ i, P₁ = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          Q₂ = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      IsReduced (pullback i₁ i₂) ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k) ∧
      Set.range i₁.base ∩ ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) : Set ↥(pullback (DRModel.toBase p) s)) =
        connectedComponentIn ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) : Set ↥(pullback (DRModel.toBase p) s)) (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
        (pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens)) ∧
      (∀ y : ↥(pullback (DRModel.toBase p) s),
        (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
          y ∈ (pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens)) ∧
      (∃ W₁ : (pullback (DRModel.toBase p) s).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) s)) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)) := by sorry
