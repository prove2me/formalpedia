-- Prove2me | Theorems.Thm_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
-- name    : NeronModelInfra.exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/9770de88-7aac-584a-82ce-4fb967c63a26
-- title:
--   Descent action on a solution of a birational group law
-- statement:
--   Let $R$ be a Henselian discrete valuation domain and $f\colon X\to\operatorname{Spec}R$ smooth, separated, locally of finite type and quasi-compact. Let $W$ be an open subscheme of $X\times_R X$, let $m$ be a morphism $W\to X$ over $\operatorname{Spec}R$ (i.e. satisfying $m\circ(\text{incl}) = f\circ\mathrm{pr}_1$ on $W$), let $X'\subseteq X$ be open and let $U\subseteq W$ be open such that every point of $X\times_R X$ not lying over the closed point of $\operatorname{Spec}R$ lies in $U$, and such that for every $q\in U$ the two projections of $q$ and $m(q)$ lie in $X'$. Let $R'$ be a discrete valuation domain which is a finite, étale and faithfully flat $R$-algebra, write $s=\operatorname{Spec}(R'\!/R)$ for the induced morphism $\operatorname{Spec}R'\to\operatorname{Spec}R$, and let $g'\colon B'\to\operatorname{Spec}R'$ be smooth, separated, locally of finite type and quasi-compact, carrying a relative group law $L_{B'}$ over $R'$, that is functorial operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on $T$-points over $\operatorname{Spec}R'$ satisfying the group axioms and compatible with composition in $T$. Let $j'$ be a morphism over $\operatorname{Spec}R'$ from the base change $X'\times_R\operatorname{Spec}R'$ (realised as the second projection of the pullback of $X'\hookrightarrow X\to\operatorname{Spec}R$ along $s$) to $B'$, whose underlying morphism is an open immersion, such that every point of $B'$ not over the closed point of $\operatorname{Spec}R'$ lies in the image of $j'$, and so does every point over the closed point which is maximal among points over the closed point specialising to it. Assume finally that $L_{B'}$ restricts to $m$ through $j'$, in the following sense: for every scheme $T$, every $t'\colon T\to\operatorname{Spec}R'$, every $T$-point $w$ of $U$ over $t'\circ s$ and all $T$-points $a,b,c$ of $X'$ over $t'\circ s$ with $a=\mathrm{pr}_1\circ w$, $b=\mathrm{pr}_2\circ w$ and $c=m\circ w$ after inclusion into $X$, the point of $X'\times_R\operatorname{Spec}R'$ determined by $c$, followed by $j'$, equals $L_{B'}$-product of the points determined by $a$ and by $b$, each followed by $j'$. The conclusion is that there is a descent action $A$ for $s$ on $g'$, i.e. a morphism $\mathrm{act}\colon B'\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to B'$ over the second projection satisfying the unit and transitivity identities, with two properties. First, $j'$ is equivariant: the morphism $B'\times_{\operatorname{Spec}R}\operatorname{Spec}R'\leftarrow (X'\times_R\operatorname{Spec}R')\times_{\operatorname{Spec}R}\operatorname{Spec}R'$ induced by $j'$, followed by $\mathrm{act}$, coincides with the canonical descent action of the base change of $X'\to\operatorname{Spec}R$ along $s$, followed by $j'$. Secondly, $\mathrm{act}$ is multiplicative: for every scheme $T$, all $\tau,t'\colon T\to\operatorname{Spec}R'$ with $t'\circ s=\tau\circ s$ and all $T$-points $x,y$ of $B'$ over $t'$, transporting $L_{B'}$-product of $x$ and $y$ by $\mathrm{act}$ (via the $\tau$-point of $B'\times_{\operatorname{Spec}R}\operatorname{Spec}R'$ it determines) gives $L_{B'}$-product over $\tau$ of the transports of $x$ and of $y$.
--
--   This isolates the step of Bosch–Lütkebohmert–Raynaud's proof of Corollary 2 in §6.5 of Néron Models in which the canonical descent datum on $X'\times_R\operatorname{Spec}R'$ is shown to extend to a descent datum on a solution $B'$ of the birational group law over the finite étale extension $R'$, compatibly with the group law. Combined with effectivity of such descent data it is used in the construction of a solution of the birational group law over $R$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b) jY')) :
    ∃ A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g',
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫ jY'.1 ∧
      (∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
          (hτ : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (x y : SchemeHomOver t' g'),
        NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
              (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
                SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (⟨A.act, A.act_comp⟩ : SchemeHomOver
              (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') =
          LB'.mul τ
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))) := by sorry
