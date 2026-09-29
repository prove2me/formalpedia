-- Prove2me | Theorems.Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha
-- name    : ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/e0d2613c-2de1-554a-b814-6c2d9b4634cc
-- title:
--   Euler characteristic of a divisorial twist on a fibre component
-- statement:
--   Fix $N_0$ nonzero and a prime $p$ with $p \nmid N_0$, a Deligne–Rapoport model package $\mathfrak{P}$ of level $N_0p$, a local ring $O$ with a ring map $\rho_O : R_p \to O$ whose maximal ideal is $(p)$, an algebraically closed field $\kappa$ of characteristic $p$ with $O \to \kappa$, and a resolved package $R$ over these data, with special-fibre components indexed by $X0MqComponents$ of $R.width$, namely $\mathrm{Fin}\,2 \sqcup \coprod_{n}\mathrm{Fin}(\mathrm{width}(n)-1)$, each carrying an ideal sheaf $R.comp$. Let $\sigma_1,\dots,\sigma_m$ be sections of $R.toBase$ over $\mathrm{Spec}\,O$, let $\mathrm{pos},\mathrm{neg} : \mathrm{Fin}\,m \to \mathbb{N}$, and let $v_j$ be components such that the image of the closed point of $O$ under $\sigma_j$ lies in the support of $R.comp(v_j)$ and in the support of no other component. Let $a^+,a^-$ assign natural numbers to components, fix a component $c$, a field $k$ and a proper $y : (R.comp\,c).subscheme \to \mathrm{Spec}\,k$ such that every edge point $R.edgePt\,n\,d$ in the support of $R.comp\,c$, and the closed point of every $\sigma_j$ with $v_j = c$, lies in the image of some section $s$ of $y$ composed with the closed immersion of the component, and fix a two-affine open cover $\mathcal{W}$ of that component. Write $\chi$ for $\dim_k H^0 - \dim_k H^1$ of the two-chart Čech complex of $\mathcal{W}.sectionsOf\,y$. Then $\chi$ of the pullback along the component's closed immersion of the module $\bigotimes_j \bigl((\ker\sigma_j)^{\mathrm{pos}_j}\bigr)^{\vee} \otimes (\ker\sigma_j)^{\mathrm{neg}_j} \otimes \bigl(\prod_F (R.comp\,F)^{a^+_F}\bigr)^{\vee} \otimes \prod_F (R.comp\,F)^{a^-_F}$ — where each ideal sheaf contributes its ideal-sheaf module and $(-)^{\vee}$ its dual, assembled by a right fold over $\mathrm{Fin}\,m$ — equals $\chi$ of the unit module plus $\bigl(\sum_j \mathrm{single}(v_j)(\mathrm{pos}_j - \mathrm{neg}_j)\bigr)(c)$, that is $\sum_{j : v_j = c}(\mathrm{pos}_j - \mathrm{neg}_j)$, plus the value at $c$ of $intersectionAlpha$ for the table $x0MqResolvedTable$ of $R.width$ applied to $F \mapsto a^+_F - a^-_F$, namely $\sum_F (a^+_F - a^-_F)\,(\mathrm{adj}(F,c) - [F = c]\sum_{F'}\mathrm{adj}(F,F'))$.
--
--   This is the Riemann–Roch style Euler-characteristic count, on a single component of the reduced special fibre of the resolved Deligne–Rapoport model of $X_0(N_0p)$, for the invertible module built from the kernel ideals of a family of sections and from the vertical component ideals: the horizontal sections contribute their multiplicities at the chosen component and the vertical part contributes through the intersection form of the subdivided dual graph. It is used to derive the vanishing $\sum_j \mathrm{single}(v_j)(\mathrm{pos}_j-\mathrm{neg}_j) + \alpha(a^+-a^-) = 0$ when the comparison map to the Deligne–Rapoport model is an isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRResolvedModelPackageLevel_eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha.lean

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra MazurRapoportAppendix
open ModularCurve
open scoped BigOperators

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRResolvedModelPackageLevel.eulerChar_sectionsOf_pullback_foldr_ker_tensor_prod_comp_eq_add_sum_single_add_intersectionAlpha
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] {hpN₀ : ¬ p ∣ N₀} {𝔓 : DRModelPackageLevel N₀ p hpN₀}
    {O : Type} [CommRing O] [IsLocalRing O] {ρO : DRLevel.R p →+* O}
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {toκ : O →+* κ}
    (R : DRResolvedModelPackageLevel N₀ p 𝔓 O ρO κ toκ)
    {m : ℕ} (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) R.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents R.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ (R.comp (v j)).support ∧
      ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (R.comp w).support)
    (aplus aminus : X0MqComponents R.width → ℕ)
    (c : X0MqComponents R.width)
    {k : Type} [Field k] (y : (R.comp c).subscheme ⟶ Spec (CommRingCat.of k)) [IsProper y]
    (hrat : ∀ (n : R.node) (d : Fin (R.width n)), R.edgePt n d ∈ (R.comp c).support →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ R.edgePt n d ∈ Set.range (s ≫ (R.comp c).subschemeι).base)
    (hratσ : ∀ j, v j = c →
      ∃ s : Spec (CommRingCat.of k) ⟶ (R.comp c).subscheme,
        s ≫ y = 𝟙 _ ∧ (σ j).1.base (IsLocalRing.closedPoint O) ∈ Set.range (s ≫ (R.comp c).subschemeι).base)
    (𝒲 : ((R.comp c).subscheme).TwoAffineOpenCover) :
    (Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj
        ((List.finRange m).foldr
          (fun j N => (((σ j).1.ker) ^ (pos j)).invModule ⊗ (((σ j).1.ker) ^ (neg j)).module ⊗ N)
          ((∏ F, (R.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (R.comp F) ^ (aminus F)).module)))).H0 : ℤ)
      - Module.finrank k (𝒲.sectionsOf y ((Scheme.Modules.pullback (R.comp c).subschemeι).obj
        ((List.finRange m).foldr
          (fun j N => (((σ j).1.ker) ^ (pos j)).invModule ⊗ (((σ j).1.ker) ^ (neg j)).module ⊗ N)
          ((∏ F, (R.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (R.comp F) ^ (aminus F)).module)))).H1
    = (Module.finrank k (𝒲.sectionsOf y (𝟙_ ((R.comp c).subscheme).Modules)).H0 : ℤ)
      - Module.finrank k (𝒲.sectionsOf y (𝟙_ ((R.comp c).subscheme).Modules)).H1
      + (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) c
      + intersectionAlpha (x0MqResolvedTable R.width) (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) c := by sorry
