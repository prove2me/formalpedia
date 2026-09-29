-- Prove2me | Theorems.Thm_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
-- name    : NeronModelInfra.exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/389c78aa-2037-5677-8467-b4967a4c58bf
-- title:
--   Gluing a smooth R-scheme to its translate by a section
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring structure), and let $y\colon Y\to\operatorname{Spec}R$ be a smooth, separated, locally of finite type and quasi-compact morphism of schemes. Let $U$ be an open subscheme of $Y\times_R Y=$ `pullback y y` and let $m\colon U\to Y$ be a morphism with $m\circ\iota_U$-compatibility over the base, i.e. $m$ followed by $y$ equals the inclusion of $U$ followed by the first projection followed by $y$. Assume: for each point $x$ of $Y$, the preimage of $U$ in the set-theoretic fibre $\{q\in Y\times_RY: \mathrm{pr}_1(q)=x\}$ (with its subspace topology) is dense, and likewise the preimage in that fibre of the image of the morphism $\Phi=(\iota_U\circ\mathrm{pr}_1,\,m)\colon U\to Y\times_RY$ is dense. Let $\gamma\colon G\to (Y\times_RY)\times_RY$ be a closed immersion whose image contains the image of the graph morphism $(\iota_U,m)\colon U\to (Y\times_RY)\times_RY$, and assume that both composites of $\gamma$ with the projection $\mathrm{pr}_{12}$ to $Y\times_RY$ and with the map $\mathrm{pr}_{13}=(\mathrm{pr}_1\circ\mathrm{pr}_{12},\mathrm{pr}_3)$ to $Y\times_RY$ are open immersions. Finally let $a\colon\operatorname{Spec}R\to Y$ be a section of $y$. Then there exist a scheme $Y'$, a morphism $y'\colon Y'\to\operatorname{Spec}R$ and two morphisms $\iota,\tau\colon Y\to Y'$ with $\iota\circ$, $\tau\circ$ followed by $y'$ equal to $y$, such that $y'$ is smooth, separated, locally of finite type and quasi-compact; $\iota$ and $\tau$ are open immersions; every point of $Y'$ lies in the image of $\iota$ or of $\tau$; every point $p$ of $Y'$ that is maximal for specialisation inside its fibre (every $p'$ specialising to $p$ with $y'(p')=y'(p)$ equals $p$) lies in the image of $\iota$, and also in the image of $\tau$; the square formed by the two projections $Y\times_RY\to Y$ restricted to the slice $\Gamma_a:=G\times_{(Y\times_RY)\times_RY}(Y\times_RY)$, taken along the closed immersion $(b,c)\mapsto((a,b),c)$, together with $\tau$ and $\iota$, is cartesian; and for every scheme $T$, every $t\colon T\to\operatorname{Spec}R$, every $x\colon T\to Y$ over $t$ and every $w\colon T\to U$ over $t$ whose first coordinate is $t$ followed by $a$ and whose second coordinate is $x$, one has $\tau\circ x=\iota\circ m\circ w$.
--
--   This is the gluing step in Artin's proof, after Weil, that a (strict) birational group law over a discrete valuation ring is induced by a group scheme: $Y$ is glued to a translate of itself by the section $a$ along the slice $\Gamma_a$ of the closure of the graph of the partial law, producing a smooth separated $R$-scheme covered by two charts each containing all points maximal for specialisation in their fibre, on which the partial translation by $a$ becomes everywhere defined. It is used in the construction of the Néron model of the Jacobian, via the statement [`NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre`](thm.html#NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_isSeparated_isOpenImmersion_isPullback_glue_translate_of_isClosedImmersion_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hγ : Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base ⊆
      Set.range γ.base)
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _) :
    ∃ (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R)) (ι τ : SchemeHomOver y y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧ IsOpenImmersion τ.1 ∧
      (∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range τ.1.base) ∧
      IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t y)
          (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        w.1 ≫ U.ι ≫ pullback.fst y y = t ≫ a → w.1 ≫ U.ι ≫ pullback.snd y y = x.1 →
        x.1 ≫ τ.1 = w.1 ≫ m.1 ≫ ι.1) := by sorry
