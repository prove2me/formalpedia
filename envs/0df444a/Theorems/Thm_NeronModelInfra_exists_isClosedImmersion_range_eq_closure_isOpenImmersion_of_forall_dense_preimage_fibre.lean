-- Prove2me | Theorems.Thm_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
-- name    : NeronModelInfra.exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e36ec287-78c3-5373-b0db-ab932ccff710
-- title:
--   Graph closure of a birational group law over a DVR
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete-valuation-ring property) and let $y : Y \to \operatorname{Spec} R$ be a morphism of schemes that is smooth, separated, locally of finite type and quasi-compact. Let $U$ be an open subscheme of the fibre product $Y \times_R Y$ (the pullback of $y$ along itself, with projections $\mathrm{pr}_1 =$ `pullback.fst y y` and $\mathrm{pr}_2 =$ `pullback.snd y y`), and let $m$ be an element of `SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y`, that is, a morphism $m : U \to Y$ together with the identity $m \circ y = y \circ \mathrm{pr}_1 \circ \iota_U$. Assume: (i) for every point $x$ of $Y$, the preimage of $U$ in the subspace $\{q \in Y \times_R Y : \mathrm{pr}_1(q) = x\}$ is dense, and likewise in $\{q : \mathrm{pr}_2(q) = x\}$; (ii) the morphism $\Phi = (\mathrm{pr}_1 \circ \iota_U,\, m) : U \to Y \times_R Y$ obtained by `pullback.lift` is an open immersion, and its set-theoretic image meets each $\mathrm{pr}_1$-fibre and each $\mathrm{pr}_2$-fibre over every point of $Y$ in a dense subset; (iii) the same for $\Psi = (m,\, \mathrm{pr}_2 \circ \iota_U) : U \to Y \times_R Y$; (iv) associativity in the form: for every scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$ and all four morphisms $u, v, p, q : T \to U$ over $\operatorname{Spec} R$ (each compatible with $t$ via $y \circ \mathrm{pr}_1 \circ \iota_U$), if the second coordinate of $u$ equals the first coordinate of $v$, the coordinates of $p$ are $m \circ u$ and the second coordinate of $v$, and the coordinates of $q$ are the first coordinate of $u$ and $m \circ v$, then $m \circ p = m \circ q$. The conclusion asserts the existence of a scheme $G$ and a morphism $\gamma : G \to (Y \times_R Y) \times_R Y$ such that $\gamma$ is a closed immersion, $G$ is reduced, the image of $\gamma$ on underlying topological spaces is exactly the closure of the image of the graph morphism $(\iota_U, m) : U \to (Y \times_R Y) \times_R Y$, the three composites of $\gamma$ with the projection to $Y \times_R Y$ and with the two morphisms $(\mathrm{pr}_1 \circ \mathrm{pr}_1, \mathrm{pr}_2)$ and $(\mathrm{pr}_2 \circ \mathrm{pr}_1, \mathrm{pr}_2)$ to $Y \times_R Y$ are all open immersions, and, for every point $x$ of $Y$, each of these three images meets the subspace of points with $\mathrm{pr}_1$-image $x$ and the subspace of points with $\mathrm{pr}_2$-image $x$ in a dense subset.
--
--   This is the scheme-theoretic form of the basic lemma in Artin's construction, after Weil, of a group scheme from a strict birational group law: a point of the closure $\Gamma$ of the graph of the partial multiplication is determined by any two of its three coordinates, so that the three projections $\Gamma \to Y \times_R Y$ are open immersions with fibrewise dense images. It is used in the subsequent steps that glue translates of $Y$ along closures of graphs of translations ([`NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre`](thm.html#NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre) and [`NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre`](thm.html#NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre)), on the way to the existence of Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_isClosedImmersion_range_eq_closure_isOpenImmersion_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
          ((Category.assoc _ _ _).trans m.2.symm)).base))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
        Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
          (m.2.trans (by rw [Category.assoc, pullback.condition]))).base))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1) :
    ∃ (G : Scheme.{u}) (γ : G ⟶ pullback (pullback.fst y y ≫ y) y),
      IsClosedImmersion γ ∧ IsReduced G ∧
      Set.range γ.base =
        closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base) ∧
      IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y) ∧
      IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition)) ∧
      IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)) ∧
      (∀ x : Y,
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.fst (pullback.fst y y ≫ y) y).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.fst (pullback.fst y y ≫ y) y).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)).base) ∧
        Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          Set.range (γ ≫ pullback.lift (f := y) (g := y)
            (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
            (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition)).base)) := by sorry
