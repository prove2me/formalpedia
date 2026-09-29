-- Prove2me | Theorems.Thm_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
-- name    : NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/f9d2c399-cddf-5993-8e46-85ccd2dfd5b9
-- title:
--   Strictness and associativity descend to a quasi-finite extension of m
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation property), $Y$ a scheme with a morphism $y \colon Y \to \operatorname{Spec} R$, $U$ an open subscheme of $Y \times_R Y =$ `pullback y y`, and $m$ a morphism $U \to Y$ over $R$, i.e. with $m$ followed by $y$ equal to the inclusion $U \hookrightarrow Y\times_R Y$ followed by $\mathrm{pr}_1$ and then $y$. Assume: for every $x \in Y$ the preimage of $U$ in the subspace $\{q : \mathrm{pr}_1(q) = x\}$ is dense; the morphism $\Phi = (\mathrm{pr}_1|_U, m) \colon U \to Y\times_R Y$ is an open immersion and, for every $x \in Y$, the preimage of the set-theoretic image of $\Phi$ in that same fibre is dense; likewise for $\Psi = (m, \mathrm{pr}_2|_U)$; and $m$ is associative in the sense that for every $t \colon T \to \operatorname{Spec} R$ and all $u,v,p,q \colon T \to U$ over $t$ with $\mathrm{pr}_2 u = \mathrm{pr}_1 v$, $\mathrm{pr}_1 p = m u$, $\mathrm{pr}_2 p = \mathrm{pr}_2 v$, $\mathrm{pr}_1 q = \mathrm{pr}_1 u$ and $\mathrm{pr}_2 q = m v$, one has $m p = m q$. Let further $y' \colon Y' \to \operatorname{Spec} R$ be smooth, separated, locally of finite type and quasi-compact, and $\iota \colon Y \to Y'$ a morphism over $R$ which is an open immersion and whose image contains every point $p$ of $Y'$ admitting no other point of the same fibre of $y'$ specialising to it. Let $U'$ be open in $Y' \times_R Y'$ and $m' \colon U' \to Y'$ a morphism over $R$ such that for every $t \colon T \to \operatorname{Spec} R$ and every $w \colon T \to U$ over $t$ there is $w' \colon T \to U'$ over $t$ with $\mathrm{pr}_1 w' = \iota\,\mathrm{pr}_1 w$, $\mathrm{pr}_2 w' = \iota\,\mathrm{pr}_2 w$ and $m' w' = \iota\, m w$. Assume finally that $\Phi' = (\mathrm{pr}_1|_{U'}, m')$ and $\Psi' = (m', \mathrm{pr}_2|_{U'})$ are locally quasi-finite. Then $\Phi'$ and $\Psi'$ are open immersions, and $m'$ satisfies the same associativity condition as $m$, with $T$-points of $U'$ in place of $T$-points of $U$.
--
--   This is the concluding step in the proof that a strict birational group law over a discrete valuation ring extends strictly along an $R$-dense open immersion into a smooth separated scheme of finite type (Bosch–Lütkebohmert–Raynaud 5.3, Lemma 5), the quasi-finiteness of the extended translations being upgraded to openness by Zariski's main theorem in the form of 2.3, Theorem 2'. It is used in the construction of the smooth group scheme obtained by gluing translates, in [`NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section`](thm.html#NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section), en route to the Néron model of a Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.isOpenImmersion_lift_and_forall_comp_eq_of_locallyQuasiFinite_of_forall_exists_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (Set.range (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver y y') [IsOpenImmersion ι.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hext : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
        w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1)
    [LocallyQuasiFinite
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
        ((Category.assoc _ _ _).trans m'.2.symm))]
    [LocallyQuasiFinite
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
        (m'.2.trans (by rw [Category.assoc, pullback.condition])))] :
    IsOpenImmersion
        (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
          ((Category.assoc _ _ _).trans m'.2.symm)) ∧
    IsOpenImmersion
        (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
          (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
      p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
      q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1) := by sorry
