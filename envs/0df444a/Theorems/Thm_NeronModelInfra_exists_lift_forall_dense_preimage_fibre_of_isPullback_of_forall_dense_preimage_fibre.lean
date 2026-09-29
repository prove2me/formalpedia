-- Prove2me | Theorems.Thm_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
-- name    : NeronModelInfra.exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/c283e9e1-87cf-5f87-a706-c699875b0052
-- title:
--   Strict birational group laws descend along base change
-- statement:
--   Let $R \to R'$ be given by a morphism $g\colon \operatorname{Spec} R' \to \operatorname{Spec} R$ of affine schemes attached to commutative rings $R, R'$, let $y\colon Y \to \operatorname{Spec} R$ be a scheme over $\operatorname{Spec} R$, let $U$ be an open subscheme of $\operatorname{pullback}\ y\ y$ and let $m$ be a morphism $U \to Y$ with $m.1 \circ y = y \circ \mathrm{pr}_1 \circ \iota_U$ (an element of `SchemeHomOver`, i.e. a pair consisting of a morphism and this commutation). Assume: for every point $x$ of $Y$, the preimage of $U$ in each of the two fibres $\{q : \mathrm{pr}_1(q) = x\}$ and $\{q : \mathrm{pr}_2(q) = x\}$ is dense; the morphism $\Phi = (\iota_U \circ \mathrm{pr}_1, m.1)$ into $\operatorname{pullback}\ y\ y$ is an open immersion and its set-theoretic image meets every such $\mathrm{pr}_1$- and $\mathrm{pr}_2$-fibre densely; likewise the morphism $\Psi = (m.1, \iota_U \circ \mathrm{pr}_2)$ is an open immersion with the same two density properties; and the associativity condition holds: for every scheme $T$ with a morphism $t$ to $\operatorname{Spec} R$ and all four $T$-points $u,v,p,q$ of $U$ over $t$ satisfying $\mathrm{pr}_2 u = \mathrm{pr}_1 v$, $\mathrm{pr}_1 p = m(u)$, $\mathrm{pr}_2 p = \mathrm{pr}_2 v$, $\mathrm{pr}_1 q = \mathrm{pr}_1 u$, $\mathrm{pr}_2 q = m(v)$, one has $m(p) = m(q)$. Let further $y'\colon Y' \to \operatorname{Spec} R'$ and $p\colon Y' \to Y$ form a pullback square of $y$ along $g$, and let $c\colon \operatorname{pullback}\ y'\ y' \to \operatorname{pullback}\ y\ y$ be compatible with both projections, $c \circ \mathrm{pr}_i = p \circ \mathrm{pr}_i'$. Then there exists a morphism $m'$ from the open subscheme $c^{-1}U$ of $\operatorname{pullback}\ y'\ y'$ to $Y'$ with $m'.1 \circ y' = y' \circ \mathrm{pr}_1' \circ \iota_{c^{-1}U}$ such that $m'.1$ followed by $p$ equals the restriction of $c$ to $c^{-1}U \to U$ followed by $m.1$, and such that all nine of the listed properties hold for $(c^{-1}U, m')$ over $\operatorname{Spec} R'$: the two fibrewise density statements for $c^{-1}U$, the open-immersion property of $\Phi' = (\iota_{c^{-1}U} \circ \mathrm{pr}_1', m'.1)$ together with the fibrewise density of its image, the same for $\Psi' = (m'.1, \iota_{c^{-1}U} \circ \mathrm{pr}_2')$, and the associativity condition for $T$-points over $\operatorname{Spec} R'$.
--
--   This is the statement that an associative strict birational group law on an $R$-scheme, in the sense of the fibrewise-density and universal-translation conditions of Bosch–Lütkebohmert–Raynaud 5.2, together with its defining data, is stable under base change $R \to R'$, the law on $Y' = Y \times_R \operatorname{Spec} R'$ being defined on $c^{-1}U$ by the universal property of the pullback. It feeds the construction of the group scheme obtained by gluing translates of such a law, used in the Néron model input to the study of Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_lift_forall_dense_preimage_fibre_of_isPullback_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
    (g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
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
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) (p : Y' ⟶ Y) (hp : IsPullback p y' y g)
    (c : pullback y' y' ⟶ pullback y y)
    (hc₁ : c ≫ pullback.fst y y = pullback.fst y' y' ≫ p) (hc₂ : c ≫ pullback.snd y y = pullback.snd y' y' ≫ p) :
    ∃ m' : SchemeHomOver ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y') y',
      m'.1 ≫ p = c.resLE U (c ⁻¹ᵁ U) le_rfl ≫ m.1 ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          ((c ⁻¹ᵁ U) : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          ((c ⁻¹ᵁ U) : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 ((c ⁻¹ᵁ U).ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t ((c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' →
        p.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' →
        q.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' = u.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.fst y' y' →
        q.1 ≫ (c ⁻¹ᵁ U).ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) := by sorry
