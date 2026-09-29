-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
-- name    : NeronModelInfra.exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/26a017f8-edba-55bf-8870-7cc1df953e0c
-- title:
--   Translated birational group law descends to an open domain
-- statement:
--   Let $R$ be a commutative ring and $y\colon Y\to\operatorname{Spec}R$ a smooth morphism; write $P=Y\times_{\operatorname{Spec}R}Y$ for the pullback of $y$ with itself. Let $U\subseteq P$ be an open subscheme and $m\colon U\to Y$ a morphism with $m$ followed by $y$ equal to $U\hookrightarrow P$ followed by $\mathrm{pr}_1$ followed by $y$. Assume: for each point $x$ of $Y$, the preimage of $U$ in the fibre $\{q\in P:\mathrm{pr}_1(q)=x\}$ is dense; the morphism $U\to P$ with components $U\hookrightarrow P\to Y$ (first projection) and $m$ is an open immersion; and the associativity condition that for all $T$ over $\operatorname{Spec}R$ and all four $T$-points $u,v,p,q$ of $U$ over $\operatorname{Spec}R$ with $\mathrm{pr}_2(u)=\mathrm{pr}_1(v)$, $\mathrm{pr}_1(p)=m(u)$, $\mathrm{pr}_2(p)=\mathrm{pr}_2(v)$, $\mathrm{pr}_1(q)=\mathrm{pr}_1(u)$ and $\mathrm{pr}_2(q)=m(v)$, one has $m(p)=m(q)$. Let $R'$ be an $R$-algebra, $y'\colon Y'\to\operatorname{Spec}R'$ a separated morphism and $\iota\colon Y\otimes_RR'\to Y'$ a morphism with $\iota$ followed by $y'$ the projection $Y\otimes_RR'\to\operatorname{Spec}R'$. Let $R''$ be an étale $R'$-algebra which is a domain and a discrete valuation ring, let $a\colon \operatorname{Spec}R''\to Y$ satisfy $a$ followed by $y$ equal to $\operatorname{Spec}R''\to\operatorname{Spec}R'\to\operatorname{Spec}R$, and let $\tau\colon Y\otimes_RR''\to Y'\otimes_{R'}R''$ be a morphism compatible with the projections to $\operatorname{Spec}R''$ and such that, for all $T$ and all $x\colon T\to Y\otimes_RR''$, $w\colon T\to U$, $v\colon T\to Y\otimes_RR'$ with $\mathrm{pr}_1(w)=a$ applied to the $R''$-component of $x$, $\mathrm{pr}_2(w)$ the $Y$-component of $x$, the $Y$-component of $v$ equal to $m(w)$ and the $R'$-component of $v$ the image of the $R''$-component of $x$, the $Y'$-component of $\tau(x)$ equals $\iota(v)$. Then there exist an open subscheme $V$ of $(Y\otimes_RR')\times_{\operatorname{Spec}R'}(Y\otimes_RR')$ and a morphism $G\colon V\to Y'$ over $\operatorname{Spec}R'$ (i.e. $G$ followed by $y'$ is the inclusion of $V$ followed by the first projection followed by the projection to $\operatorname{Spec}R'$) such that: (i) for all $T$ and all $s\colon T\to V$, $w\colon T\to U$, $v\colon T\to Y\otimes_RR'$ whose $Y$-components satisfy $\mathrm{pr}_1(w)$ equal to the $Y$-part of the first coordinate of $s$, $\mathrm{pr}_2(w)$ equal to the $Y$-part of the second coordinate of $s$, the $Y$-component of $v$ equal to $m(w)$ and the $R'$-component of $v$ equal to that of the first coordinate of $s$, one has $G(s)=\iota(v)$; and (ii) for all $T$, $t\colon T\to\operatorname{Spec}R''$, $w_1,w_2\colon T\to U$ and $s\colon T\to(Y\otimes_RR')\times_{\operatorname{Spec}R'}(Y\otimes_RR')$ with $\mathrm{pr}_1(w_1)=a\circ t$, $\mathrm{pr}_1(w_2)=\mathrm{pr}_2(w_1)$, the $Y$-part of the first coordinate of $s$ equal to $m(w_1)$, the $Y$-part of the second coordinate of $s$ equal to $\mathrm{pr}_2(w_2)$, and the $R'$-component of the first coordinate of $s$ the image of $t$ under $\operatorname{Spec}R''\to\operatorname{Spec}R'$, the set-theoretic image of $s$ is contained in $V$.
--
--   This is the finite-level form of the step in the construction of a group scheme from a strict birational group law in which a left translation defined after an étale base change to a discrete valuation ring forces the law, one level down over $R'$, to be defined at the translated points, the domain of definition descending because the target is separated. It feeds into [`NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing), which assembles such open domains over henselian local bases in the construction of the Néron model used for the good-reduction input on Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_forall_range_subset_of_comp_translation_eq_of_etale.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_forall_range_subset_of_comp_translation_eq_of_etale
    {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [Smooth y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R')) [IsSeparated y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Algebra.Etale R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y)
    (ha : a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶
      pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))))
    (hτ₁ : τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) =
      pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
    (hτ₂ : ∀ {T : Scheme.{u}}
        (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
        (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
      w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
      w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
      v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
      v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
      x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (V : (pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))).Opens)
      (G : SchemeHomOver (V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
        (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'),
      (∀ {T : Scheme.{u}} (s : T ⟶ (V : Scheme.{u})) (w : T ⟶ (U : Scheme.{u}))
          (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
        s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫ pullback.fst y y →
        s ≫ V.ι ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ U.ι ≫ pullback.snd y y →
        v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
        v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          s ≫ V.ι ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
            pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        s ≫ G.1 = v ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'')) (w₁ w₂ : T ⟶ (U : Scheme.{u}))
          (s : T ⟶ pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))),
        w₁ ≫ U.ι ≫ pullback.fst y y = t ≫ a →
        w₂ ≫ U.ι ≫ pullback.fst y y = w₁ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₁ ≫ m.1 →
        s ≫ pullback.snd (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w₂ ≫ U.ι ≫ pullback.snd y y →
        s ≫ pullback.fst (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
            (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫
          pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) =
          t ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
        Set.range s.base ⊆ (V : Set ↑(pullback (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
          (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))))))) := by sorry
