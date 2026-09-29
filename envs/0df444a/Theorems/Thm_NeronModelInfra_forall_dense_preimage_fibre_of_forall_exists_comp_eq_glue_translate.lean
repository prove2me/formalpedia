-- Prove2me | Theorems.Thm_NeronModelInfra_forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate
-- name    : NeronModelInfra.forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/25126c88-6530-5a46-a755-25051baf6d2e
-- title:
--   Fibrewise density of U' and its translations after gluing
-- statement:
--   Let $R$ be a noetherian commutative ring, let $y : Y \to \operatorname{Spec} R$ be separated, locally of finite type and quasi-compact, let $U$ be an open subscheme of $Y \times_R Y$ and let $m$ be a morphism $U \to Y$ over $\operatorname{Spec} R$ with $m \circ{} =$ the composite of $U \hookrightarrow Y\times_R Y$, $\mathrm{pr}_1$ and $y$. Assume that, for every point $x$ of $Y$, the preimage of $U$ in the subspace $\{q : \mathrm{pr}_1(q) = x\}$ and in $\{q : \mathrm{pr}_2(q) = x\}$ is dense, and likewise for the set-theoretic image of $\Phi = (\mathrm{pr}_1|_U, m)$ and of $\Psi = (m, \mathrm{pr}_2|_U)$ into $Y\times_R Y$, with $\Psi$ moreover an open immersion. Let $a$ be a section of $y$. Let $y' : Y' \to \operatorname{Spec} R$ be locally of finite type and quasi-compact and let $\iota, \tau : Y \to Y'$ be morphisms over $\operatorname{Spec} R$ which are open immersions, whose images cover $Y'$ and each of which contains every point of $Y'$ that is maximal for specialisation inside its fibre of $y'$. Let $U'$ be open in $Y' \times_R Y'$ and $m' : U' \to Y'$ a morphism over $\operatorname{Spec} R$ satisfying, for all $T$-valued data over $\operatorname{Spec} R$: every point of $U$ maps through $(\iota,\iota)$, resp. $(\tau,\iota)$, into $U'$ with $m'$-value $\iota \circ m$, resp. $\tau \circ m$; and for $u, v$ in $U$ and $d$ in $Y$ with $\mathrm{pr}_2(u) = a_T$, $\mathrm{pr}_1(v) = m(u)$, $\mathrm{pr}_2(v) = d$, the pair $(\iota\,\mathrm{pr}_1(u), \tau d)$ lies in $U'$ with $m'$-value $\iota\, m(v)$. Then $U'$, the image of $\Phi' = (\mathrm{pr}_1|_{U'}, m')$ and the image of $\Psi' = (m', \mathrm{pr}_2|_{U'})$ are each dense in the subspace of $Y'\times_R Y'$ cut out by $\mathrm{pr}_1(q) = x$ and in the one cut out by $\mathrm{pr}_2(q) = x$, for every point $x$ of $Y'$.
--
--   This is the density half of Lemma 5 of §5.3 of Bosch–Lütkebohmert–Raynaud: it transports the fibrewise density conditions on a birational group law $(U, m)$ on $Y$ to the law $(U', m')$ on the scheme $Y'$ glued from two copies of $Y$ along $\iota$ and $\tau$. It feeds the construction of the smooth model with a birational group law used in the Néron model input to good reduction of Jacobians, via [`NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section`](thm.html#NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.forall_dense_preimage_fibre_of_forall_exists_comp_eq_glue_translate
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hU₂ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.snd y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
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
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hcov : ∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base)
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (hτd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range τ.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hext : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
        w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1)
    (hp1 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ τ.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
        w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ τ.1)
    (hp2 : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : SchemeHomOver t y)
        (u v : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = t ≫ a →
      v.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → v.1 ≫ U.ι ≫ pullback.snd y y = d.1 →
      ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = d.1 ≫ τ.1 ∧
        w'.1 ≫ m'.1 = v.1 ≫ m.1 ≫ ι.1) :
    (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
        (U' : Set ↑(pullback y' y')))) ∧
    (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
        (U' : Set ↑(pullback y' y')))) ∧
    (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
        (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
          ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
    (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
        (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
          ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
    (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
        (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
          (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
    (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
        (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
          (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) := by sorry
