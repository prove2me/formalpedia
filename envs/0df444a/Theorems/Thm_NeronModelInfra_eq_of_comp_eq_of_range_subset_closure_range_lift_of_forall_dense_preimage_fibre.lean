-- Prove2me | Theorems.Thm_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
-- name    : NeronModelInfra.eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/3d9bb756-1c75-50a5-81c7-b28b35a4b0ca
-- title:
--   Field-valued points of a birational group law graph closure
-- statement:
--   Let $R$ be a noetherian integral domain and let $y \colon Y \to \operatorname{Spec} R$ be smooth, separated and locally of finite type. Let $U$ be an open subscheme of $Y \times_R Y$ and let $m$ be a pair consisting of a morphism $U \to Y$ together with the condition that it commutes with the structure morphisms, the one on $U$ being its inclusion followed by the first projection and then $y$; write $(a,b) \mapsto ab$ for $m$. Assume: for every point $x$ of $Y$, the part of $U$ lying in the fibre $\mathrm{pr}_1^{-1}(x)$ is dense in that fibre (as a subspace of $Y\times_R Y$ cut out by $\mathrm{pr}_1(q)=x$); the morphisms $(\mathrm{pr}_1,m)$ and $(m,\mathrm{pr}_2)$ from $U$ to $Y\times_R Y$ are open immersions; and $m$ is associative in the sense that for every $T \to \operatorname{Spec} R$ and all four $T$-points $u,v,p,q$ of $U$ over $\operatorname{Spec} R$ with $\mathrm{pr}_2 \circ u = \mathrm{pr}_1 \circ v$ (so $u=(a,b)$, $v=(b,c)$), $p = (ab,c)$ and $q=(a,bc)$ in the sense that the displayed coordinate identities hold, one has $m \circ p = m \circ q$. Let $K$ be a field and let $g,g'$ be two $K$-points of $(Y\times_R Y)\times_R Y$ whose underlying topological images lie in the closure of the image of the graph morphism $U \to (Y\times_R Y)\times_R Y$, $(a,b)\mapsto ((a,b),ab)$. Then each of the three projections $((a,b),c) \mapsto (a,b)$, $((a,b),c)\mapsto (a,c)$ and $((a,b),c)\mapsto (b,c)$ separates $g$ from $g'$: if $g$ and $g'$ have the same composite with any one of them, then $g = g'$.
--
--   This is the injectivity half of the statement that the three projections of the graph closure of a strict birational group law to $Y\times_R Y$ are injective (Bosch–Lütkebohmert–Raynaud, Néron Models, 5.3), phrased for field-valued points of the ambient triple product lying in the closure rather than for a scheme structure on it. It is used in the construction of a group scheme from a birational group law, being cited in the production of a closed immersion whose range is the closure of the graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.eq_of_comp_eq_of_range_subset_closure_range_lift_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
        (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1 ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {K : Type u} [Field K] (g g' : Spec (CommRingCat.of K) ⟶ pullback (pullback.fst y y ≫ y) y)
    (hg : Set.range g.base ⊆
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    (hg' : Set.range g'.base ⊆
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base)) :
    (g ≫ pullback.fst (pullback.fst y y ≫ y) y = g' ≫ pullback.fst (pullback.fst y y ≫ y) y → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition) → g = g') ∧
    (g ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) =
      g' ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition) → g = g') := by sorry
