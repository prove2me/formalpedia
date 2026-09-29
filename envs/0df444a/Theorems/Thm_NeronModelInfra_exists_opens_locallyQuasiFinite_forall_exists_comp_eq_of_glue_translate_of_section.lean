-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
-- name    : NeronModelInfra.exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9444e387-0b4d-5bb8-8476-c3bacc0e6016
-- title:
--   Birational group law on a glued translate, with quasi-finite translations
-- statement:
--   Let $R$ be a noetherian integral domain and let $y\colon Y\to\operatorname{Spec}R$ be smooth and separated. Let $U$ be an open subscheme of $Y\times_R Y$ and let $m$ be a morphism $U\to Y$ over $\operatorname{Spec}R$, i.e. an element of the subtype of morphisms $\varphi$ with $\varphi\circ y=\iota_U$ followed by $\mathrm{pr}_1$ followed by $y$. Assume: for each point $x$ of $Y$ the set $U$ pulls back to a dense subset of the fibre $\{q\in Y\times_RY:\mathrm{pr}_1(q)=x\}$; the two universal translations $(\mathrm{pr}_1\circ\iota_U,m)$ and $(m,\mathrm{pr}_2\circ\iota_U)\colon U\to Y\times_RY$ are open immersions; and $m$ is associative on points, in the sense that for every $t\colon T\to\operatorname{Spec}R$ and every four $T$-points $u,v,p,q$ of $U$ over $t$ with $\mathrm{pr}_2u=\mathrm{pr}_1v$, $\mathrm{pr}_1p=mu$, $\mathrm{pr}_2p=\mathrm{pr}_2v$, $\mathrm{pr}_1q=\mathrm{pr}_1u$ and $\mathrm{pr}_2q=mv$, one has $mp=mq$. Let $\gamma\colon G\to (Y\times_RY)\times_RY$ be a closed immersion whose set-theoretic image is the closure of the image of $(\iota_U,m)$, and let $a$ be a section of $y$. Let $y'\colon Y'\to\operatorname{Spec}R$ be smooth, separated, locally of finite type and quasi-compact, and let $\iota,\tau\colon Y\to Y'$ be morphisms over $\operatorname{Spec}R$ which are open immersions, such that every point of $Y'$ admitting no proper specialisation-predecessor in its own fibre over $\operatorname{Spec}R$ lies in the image of $\iota$, and such that on the fibre product $\Gamma_a=G\times_{(Y\times_RY)\times_RY}(Y\times_RY)$ taken along $(b,c)\mapsto((a,b),c)$ the compositions with $\mathrm{pr}_1$ followed by $\tau$ and with $\mathrm{pr}_2$ followed by $\iota$ agree. Then there are an open subscheme $U'\subseteq Y'\times_RY'$ and a morphism $m'\colon U'\to Y'$ over $\operatorname{Spec}R$ such that both universal translations $(\mathrm{pr}_1\circ\iota_{U'},m')$ and $(m',\mathrm{pr}_2\circ\iota_{U'})\colon U'\to Y'\times_RY'$ are locally quasi-finite, and such that: for every $t\colon T\to\operatorname{Spec}R$ and every $T$-point $w$ of $U$ over $t$ there is a $T$-point $w'$ of $U'$ over $t$ with coordinates $\iota\circ\mathrm{pr}_1w$, $\iota\circ\mathrm{pr}_2w$ and with $m'w'=\iota\circ mw$; likewise one with coordinates $\tau\circ\mathrm{pr}_1w$, $\iota\circ\mathrm{pr}_2w$ and $m'w'=\tau\circ mw$; and for every $t$, every $T$-point $d$ of $Y$ over $t$ and all $T$-points $u,v$ of $U$ over $t$ with $\mathrm{pr}_2u=a\circ t$, $\mathrm{pr}_1v=mu$ and $\mathrm{pr}_2v=d$, a $T$-point $w'$ of $U'$ with coordinates $\iota\circ\mathrm{pr}_1u$ and $\tau\circ d$ and with $m'w'=\iota\circ mv$. Note that the conclusion asserts only local quasi-finiteness of the two universal translations of $m'$, not that they are open immersions as assumed for $m$.
--
--   This is the extension step for strict birational group laws in the construction of Néron models (Bosch–Lütkebohmert–Raynaud, Néron Models, 5.3, Lemma 5): the birational group law on $U\subseteq Y\times_RY$ is carried over to three translated charts inside $Y'\times_RY'$, where $Y'$ is glued from $Y$ and its left translate by the section $a$. It feeds the subsequent statement on density of the fibre-preimages for the extended chart, within the Néron model infrastructure used for good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_locallyQuasiFinite_forall_exists_comp_eq_of_glue_translate_of_section
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y]
    (U : (pullback y y).Opens) (m : SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y)
    (hU₁ : ∀ x : Y,
      Dense ((Subtype.val : {q : ↑(pullback y y) // (pullback.fst y y).base q = x} → ↑(pullback y y)) ⁻¹'
          (U : Set ↑(pullback y y))))
    (hΦ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) (U.ι ≫ pullback.fst y y) m.1
            ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := y) (g := y) m.1 (U.ι ≫ pullback.snd y y)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hassoc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (u v p q : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
      u.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.fst y y →
      p.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → p.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ U.ι ≫ pullback.snd y y →
      q.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ U.ι ≫ pullback.fst y y → q.1 ≫ U.ι ≫ pullback.snd y y = v.1 ≫ m.1 →
      p.1 ≫ m.1 = q.1 ≫ m.1)
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hιd : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (hΓa : pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y ≫ τ.1 =
          pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y ≫ ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      LocallyQuasiFinite
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ τ.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ τ.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (d : SchemeHomOver t y)
          (u v : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        u.1 ≫ U.ι ≫ pullback.snd y y = t ≫ a →
        v.1 ≫ U.ι ≫ pullback.fst y y = u.1 ≫ m.1 → v.1 ≫ U.ι ≫ pullback.snd y y = d.1 →
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = d.1 ≫ τ.1 ∧
          w'.1 ≫ m'.1 = v.1 ≫ m.1 ≫ ι.1) := by sorry
