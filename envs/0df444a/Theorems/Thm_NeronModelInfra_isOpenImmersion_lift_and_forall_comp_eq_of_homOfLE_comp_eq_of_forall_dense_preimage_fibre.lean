-- Prove2me | Theorems.Thm_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
-- name    : NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/185a422b-0474-54df-9082-358921c34293
-- title:
--   Strict birational group laws extend to larger open domains
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring structure), let $Y$ be a scheme and let $y \colon Y \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact. Let $U$ be an open subscheme of $Y \times_R Y$ and let $m$ be a morphism $U \to Y$ with $m$ followed by $y$ equal to the inclusion $U.\iota$ followed by $\mathrm{pr}_1$ followed by $y$. Assume: for every point $x$ of $Y$, the preimage of $U$ in the subspace $\{q : \mathrm{pr}_1(q) = x\}$ of $Y \times_R Y$ is dense, and likewise in $\{q : \mathrm{pr}_2(q) = x\}$; the morphism $\Phi = (U.\iota \circ \mathrm{pr}_1, m) \colon U \to Y \times_R Y$ obtained by the pullback universal property is an open immersion, and the preimage of the set-theoretic range of $\Phi$ in each of the two kinds of fibre subspaces above is dense for every $x$; the same three conditions for $\Psi = (m, U.\iota \circ \mathrm{pr}_2)$; and the associativity condition: for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and all four morphisms $u, v, p, q \colon T \to U$ over $t$ (each composing with $U.\iota$ followed by $\mathrm{pr}_1$ followed by $y$ to give $t$) satisfying $u \cdot (U.\iota \circ \mathrm{pr}_2) = v \cdot (U.\iota \circ \mathrm{pr}_1)$, $p \cdot (U.\iota \circ \mathrm{pr}_1) = u \cdot m$, $p \cdot (U.\iota \circ \mathrm{pr}_2) = v \cdot (U.\iota \circ \mathrm{pr}_2)$, $q \cdot (U.\iota \circ \mathrm{pr}_1) = u \cdot (U.\iota \circ \mathrm{pr}_1)$ and $q \cdot (U.\iota \circ \mathrm{pr}_2) = v \cdot m$ (composites written in diagrammatic order), one has $p$ followed by $m$ equal to $q$ followed by $m$. Let further $D$ be an open subscheme of $Y \times_R Y$ with $U \le D$ and let $M \colon D \to Y$ satisfy the analogous compatibility with $y$ and restrict to $m$, in the sense that the inclusion morphism $U \to D$ followed by $M$ equals $m$. The conclusion is the conjunction of the nine corresponding assertions for $D$ and $M$: density of the preimage of $D$ in both families of fibre subspaces; that $\Phi_M = (D.\iota \circ \mathrm{pr}_1, M)$ is an open immersion with dense preimage of its range in both families of fibre subspaces; the same for $\Psi_M = (M, D.\iota \circ \mathrm{pr}_2)$; and the associativity condition stated with $D$, $D.\iota$ and $M$ in place of $U$, $U.\iota$ and $m$.
--
--   This is the persistence of strictness of a birational group law over a discrete valuation ring under enlargement of its domain of definition, as in the discussion following Lemma 3 of §5.3 of Bosch–Lütkebohmert–Raynaud: both the open-immersion property of the two universal translations and the associativity identity, being identities of rational maps, survive on any open domain on which the group law extends. It is used in the construction of Néron models, via [`NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_homOfLE_comp_eq_of_forall_dense_preimage_fibre
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
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΦ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (D : (pullback y y).Opens) (hUD : U ≤ D)
    (M : SchemeHomOver (D.ι ≫ pullback.fst y y ≫ y) y)
    (hM : (pullback y y).homOfLE hUD ≫ M.1 = m.1) :
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (D : Set ↑(pullback y y)))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (D : Set ↑(pullback y y)))) ∧
      IsOpenImmersion
          (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (D.ι ≫ pullback.fst y y) M.1
            ((Category.assoc _ _ _).trans M.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) M.1 (D.ι ≫ pullback.snd y y)
            (M.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (D.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.fst y y →
        p.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ M.1 →
        p.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ D.ι ≫ pullback.snd y y →
        q.1 ≫ D.ι ≫ pullback.fst y y = u.1 ≫ D.ι ≫ pullback.fst y y →
        q.1 ≫ D.ι ≫ pullback.snd y y = v.1 ≫ M.1 →
        p.1 ≫ M.1 = q.1 ≫ M.1) := by sorry
