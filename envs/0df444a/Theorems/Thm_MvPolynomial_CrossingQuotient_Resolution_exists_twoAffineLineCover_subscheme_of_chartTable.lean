-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable
-- name    : MvPolynomial.CrossingQuotient.Resolution.exists_twoAffineLineCover_subscheme_of_chartTable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/7433fc5a-d4fb-55be-ac17-579d0145e908
-- title:
--   Exceptional subschemes of the resolution covered by two affine lines
-- statement:
--   Let $W$ be a commutative ring, $t \in W$ and $e \in \mathbb{N}$, and write $A = \mathrm{MvPolynomial}\,(\mathrm{Fin}\,2)\,W/(X_0X_1 - t)$ for [`MvPolynomial.CrossingQuotient W t`](def/MvPolynomial_CrossingQuotient.html#L11), with $U$, $V$ the classes of $X_0$, $X_1$; let $\mathcal{R} =$ `Resolution t e` be the scheme obtained as the colimit of the glueing diagram `glueDiagram t e`, with structure morphism `toSpec t e` to $\operatorname{Spec} W$ (namely `toCrossing t e` followed by $\operatorname{Spec}$ of $W \to \mathrm{CrossingQuotient}\,W\,(t^e)$), and let `ι t e i`, for $i : \mathrm{Fin}\,e$, be the chart morphisms $\operatorname{Spec} A \to \mathcal{R}$. Given a family $F : \mathrm{Fin}(e+1) \to \mathcal{R}.\mathrm{IdealSheafData}$ whose chart table is prescribed by the hypothesis $hF$: for all $i : \mathrm{Fin}\,e$ and $k : \mathrm{Fin}(e+1)$, the comap of $F_k$ along `ι t e i` is the ideal sheaf data attached to the ideal of $\Gamma(\operatorname{Spec} A)$ corresponding, under the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism of $A$, to $(V)$ if $k = i$, to $(U)$ if $k = i+1$, and to the whole ring otherwise. Let $d$ satisfy $0 < d < e$, and let $k_0$ be a field which is a $W$-algebra such that $W \to k_0$ is surjective with kernel $(t)$. Then, writing $Z$ for the closed subscheme `(F ⟨d,_⟩).subscheme` with inclusion `subschemeι`, there exist a morphism $z : Z \to \operatorname{Spec} k_0$ and open immersions $i_0, i_1 : \operatorname{Spec} k_0[X] \to Z$ such that: $z$ followed by $\operatorname{Spec}$ of $W \to k_0$ equals the inclusion of $Z$ followed by `toSpec t e`; each $i_j$ followed by $z$ is $\operatorname{Spec}$ of $k_0 \to k_0[X]$; the images of the underlying maps of $i_0$ and $i_1$ cover $Z$; the localisation $\operatorname{Spec} k_0[X]_X \to \operatorname{Spec} k_0[X]$ followed by $i_0$ coincides with $\operatorname{Spec}$ of the $k_0$-algebra map $k_0[X] \to k_0[X]_X$ sending $X$ to the inverse of $X$, followed by $i_1$; the intersection of the images of $i_0$ and $i_1$ is contained in the image of that localisation composed with $i_0$; and the image of $i_0$ (resp. $i_1$) in $\mathcal{R}$ lies in the image of the chart `ι t e ⟨d-1,_⟩` (resp. `ι t e ⟨d,_⟩`).
--
--   This is the local model computation for the rationality of the exceptional curves of the $A_{e-1}$ resolution of $uv = t^e$: the $d$-th exceptional subscheme is the line $V = 0$ in chart $d-1$ glued to the line $U = 0$ in chart $d$ along the transition $X \mapsto X^{-1}$, so it is covered by two copies of $\mathbb{A}^1_{k_0}$ glued by inversion. The conclusion is shaped as the hypothesis bundle of a recognition criterion for such two-chart covers, and it is used by [`V3AsmLevel.exc_rational`](thm.html#V3AsmLevel.exc_rational) and [`V3Asm.exc_rational`](thm.html#V3Asm.exc_rational).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_exists_twoAffineLineCover_subscheme_of_chartTable.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.exists_twoAffineLineCover_subscheme_of_chartTable
    {W : Type u} [CommRing W] (t : W) (e : ℕ)
    (F : Fin (e + 1) → (MvPolynomial.CrossingQuotient.Resolution t e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (MvPolynomial.CrossingQuotient.Resolution.ι t e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial.CrossingQuotient W t))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {MvPolynomial.CrossingQuotient.V t} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {MvPolynomial.CrossingQuotient.U t} else ⊤)))
    (d : ℕ) (hd0 : 0 < d) (hde : d < e)
    (k₀ : Type u) [Field k₀] [Algebra W k₀] (hq : Function.Surjective (algebraMap W k₀))
    (hker : RingHom.ker (algebraMap W k₀) = Ideal.span {t}) :
    ∃ (z : (F ⟨d, by omega⟩).subscheme ⟶ Spec (CommRingCat.of k₀))
      (i₀ i₁ : Spec (CommRingCat.of (Polynomial k₀)) ⟶ (F ⟨d, by omega⟩).subscheme),
      IsOpenImmersion i₀ ∧ IsOpenImmersion i₁ ∧
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap W k₀)) = (F ⟨d, by omega⟩).subschemeι ≫ MvPolynomial.CrossingQuotient.Resolution.toSpec t e ∧
      i₀ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) ∧
      i₁ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap k₀ (Polynomial k₀))) ∧
      Set.range i₀.base ∪ Set.range i₁.base = Set.univ ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) ≫ i₀ =
        Spec.map (CommRingCat.ofHom (Polynomial.aeval (R := k₀)
          (IsLocalization.Away.invSelf (S := Localization.Away (Polynomial.X : Polynomial k₀)) (Polynomial.X : Polynomial k₀))).toRingHom) ≫ i₁ ∧
      Set.range i₀.base ∩ Set.range i₁.base ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k₀) (Localization.Away (Polynomial.X : Polynomial k₀)))) ≫ i₀).base ∧
      Set.range (i₀ ≫ (F ⟨d, by omega⟩).subschemeι).base ⊆ Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d - 1, by omega⟩).base ∧
      Set.range (i₁ ≫ (F ⟨d, by omega⟩).subschemeι).base ⊆ Set.range (MvPolynomial.CrossingQuotient.Resolution.ι t e ⟨d, hde⟩).base := by sorry
