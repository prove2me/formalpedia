-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth_iso_comp_eq
-- name    : ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth_iso_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7c4bc441-ebc2-5172-b20e-0e71d840614a
-- title:
--   Two-line degeneration with named components of the X₀(p) fibre
-- statement:
--   Let $p$ be a prime and let $\mathfrak X$ be a Deligne–Rapoport package `DRModelPackage p` for the two-chart integral model $\mathtt{DRModel}\,p \to \operatorname{Spec}\mathbf Z$ (carrying, among its data, a smooth open locus `𝔛.smoothLocus` maximal among opens smooth over $\mathbf Z$, a section $\varepsilon_\infty$ of the structure map, and, over an algebraically closed field of characteristic $p$, a named rational model `𝔛.ratModel` with two component maps `𝔛.compInf`, `𝔛.compZero`). The assertion is: for every algebraically closed field $k$ of characteristic $p$, if the projection $\mathfrak X_k := \mathtt{DRModel}\,p \times_{\operatorname{Spec}\mathbf Z} \operatorname{Spec} k \to \operatorname{Spec} k$ is not smooth, then there exist two curve models $M_1, M_2$ of $k(t)$ over $k$ (integral proper schemes, smooth of relative dimension $1$ over $\operatorname{Spec} k$, with a ring isomorphism of $k(t)$ onto the function field compatible with $k$, a bijection `placeEquiv` from closed points to places of $k(t)/k$ matching stalks with valuation subrings, and every finite set of points contained in an affine open), closed immersions $i_1 : M_1 \to \mathfrak X_k$, $i_2 : M_2 \to \mathfrak X_k$, an $n \in \mathbf N$, families $a, b : \mathrm{Fin}\,n \to k^\times$, and a cover $\mathcal W_0$ of $\mathfrak X_k$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and affine intersection, such that: $i_1, i_2$ are morphisms over $\operatorname{Spec} k$, i.e. $i_j$ followed by $\mathtt{pullback.snd}$ is $M_j.\mathtt{toBase}$; the images of $i_1$ and $i_2$ cover $\mathfrak X_k$; $a$ is injective; writing $P_j(c)$ for the closed point of $M_j$ at the place $t = c$ and $P_j(\infty)$ for the one at the infinite place, $i_1(P_1(a_i)) = i_2(P_2(b_i))$ for all $i$, and conversely every coincidence $i_1(P) = i_2(Q)$ is of this form for some $i$; the scheme-theoretic intersection $M_1 \times_{\mathfrak X_k} M_2$ is reduced; $i_j^{-1}U_0 = M_j \setminus \{P_j(\infty)\}$ and $i_j^{-1}U_1 = M_j \setminus \{P_j(0)\}$ for $j = 1, 2$; $i_1(P_1(\infty))$ is the point of $\mathfrak X_k$ cut out by $\varepsilon_\infty$ over the closed point of $\operatorname{Spec} k$; the image of $i_1$ meets the preimage of `𝔛.smoothLocus` in exactly the connected component of that open set containing the $\varepsilon_\infty$ point; the points $i_1(P_1(a_i))$ lie outside the preimage of `𝔛.smoothLocus` while every other point of $\mathfrak X_k$ lies inside it; the complement of the image of $i_2$ is open and the restriction of $i_1$ over it is an open immersion; and finally there are isomorphisms $e_1 : M_1 \cong (\mathtt{𝔛.ratModel}\,k).C$ and $e_2 : M_2 \cong (\mathtt{𝔛.ratModel}\,k).C$ with $e_1$ followed by `𝔛.compInf k` equal to $i_1$ and $e_2$ followed by `𝔛.compZero k` equal to $i_2$, so that the images of $i_1$, $i_2$ are the images of `𝔛.compInf k`, `𝔛.compZero k`.
--
--   This is the structure of the geometric fibre at $p$ of the Deligne–Rapoport model of $X_0(p)$: two rational curves crossing transversally at finitely many points (the supersingular points), each of which is the complement of the other's image in the smooth locus; the statement differs from the bare two-line degeneration in identifying the two lines with the package's named components $\mathtt{compInf}$ and $\mathtt{compZero}$ up to automorphisms of the rational model. It is used in the analysis of divisorial line bundles of multidegree zero on fibres of the resolved model, towards the Jacobian of $X_0(p)$ in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackage_exists_twoLineDegeneration_of_not_smooth_iso_comp_eq.lean

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

theorem ModularCurve.DRModelPackage.exists_twoLineDegeneration_of_not_smooth_iso_comp_eq (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)] [CharP k p],
    ¬ Smooth (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) →
    ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) (i₂ : M₂.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))
      (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
      (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).TwoAffineOpenCover),
      i₁ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) = M₁.toBase ∧ i₂ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) = M₂.toBase ∧
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
      i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k) ∧
      Set.range i₁.base ∩ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) =
        connectedComponentIn ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens) : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) (((sectionFibrePoint 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).1).base (IsLocalRing.closedPoint k)) ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)) ∧
      (∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))),
        (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
          y ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens)) ∧
      (∃ W₁ : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁)) ∧
      (∃ (e₁ : M₁.C ≅ (𝔛.ratModel k).C) (e₂ : M₂.C ≅ (𝔛.ratModel k).C),
        e₁.hom ≫ 𝔛.compInf k = i₁ ∧ e₂.hom ≫ 𝔛.compZero k = i₂) ∧
      Set.range i₁.base = Set.range (𝔛.compInf k).base ∧
      Set.range i₂.base = Set.range (𝔛.compZero k).base := by sorry
