-- Prove2me | Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion
-- name    : NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/84789a23-5e01-565b-aa31-9add18ddf155
-- title:
--   Descent of a solution of a birational group law along R'/R
-- statement:
--   Throughout, $R$ is a discrete valuation ring (a commutative domain with `IsDiscreteValuationRing`) and $K$ is a field which is an $R$-algebra and a fraction field of $R$; `specGenericFibreInclusion R K` denotes the induced morphism $\operatorname{Spec} K \to \operatorname{Spec} R$, and for a structure morphism $h \colon Z \to \operatorname{Spec} R$ the generic fibre is $\operatorname{pullback.snd}\,h\,(\mathrm{specGenericFibreInclusion}\,R\,K) \colon Z \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$. A `RelativeGroupLaw` over a base ring is a group law in the functor-of-points form: for every scheme $T$ and every morphism $t$ from $T$ to the base spectrum it gives operations `mul`, `one`, `inv` on the set `SchemeHomOver t h` of morphisms $T \to Z$ over $t$, subject to associativity, the two unit laws, left inverse, and naturality in $T$. For composable families, `schemeHomOverComp` composes a point with a morphism over the base; `RelativeGroupLaw.baseChangePointOfBase` turns a point over $t' \circ \iota$ of $h$ into a point over $t'$ of the base-changed structure morphism $\operatorname{pullback.snd}\,h\,\iota$, and `RelativeGroupLaw.genericFibre` is the base change of a relative group law along `specGenericFibreInclusion R K`.
--
--   Given data. A scheme $XK$ with a morphism $gK \colon XK \to \operatorname{Spec} K$ and a relative group law $LXK$ on $gK$; a scheme $X$ with $f \colon X \to \operatorname{Spec} R$ which is smooth, separated, locally of finite type and quasi-compact; a morphism $e$ from the generic fibre of $f$ to $XK$ over $\operatorname{Spec} K$ whose underlying scheme morphism is an isomorphism; an open subscheme $W$ of $X \times_{\operatorname{Spec} R} X$ and a morphism $m \colon W \to X$ over $\operatorname{Spec} R$ (an element of `SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f`).
--
--   The hypothesis `hmK` states that $m$ induces the group law of $LXK$ on generic fibres: the generic-fibre restriction of $m$ followed by $e$ equals the canonical morphism from the generic fibre of $W$ to the generic fibre of $X \times_{\operatorname{Spec} R} X$ (the pullback comparison along $W.\iota$ and the identities) followed by the underlying morphism of $LXK.\mathrm{mul}$ applied to the generic-fibre restrictions, transported by $e$, of the two projections $\operatorname{pullback.fst} f f$ and $\operatorname{pullback.snd} f f$.
--
--   Further there are an open subscheme $X'$ of $X$, an open subscheme $U$ of $X \times_{\operatorname{Spec} R} X$ with $U \le W$ (`hUW`), and three containment hypotheses: `hX'₁`, every point of $X$ whose image under $f$ is not the closed point of $R$ lies in $X'$; `hU₁`, every point $q$ of $X \times_{\operatorname{Spec} R} X$ whose image under $\operatorname{pullback.fst} f f$ followed by $f$ is not the closed point of $R$ lies in $U$; and `hU₂`, for every $q \in U$ the images of $q$ under both projections lie in $X'$ and the image of $q$ (viewed in $W$ via `hUW`) under $m$ lies in $X'$.
--
--   On the covering side, $R'$ is a discrete valuation ring which is an $R$-algebra, finite as an $R$-module, étale over $R$ and faithfully flat over $R$; write $s = \operatorname{Spec}$ of the structure map $R \to R'$. There are a scheme $B'$ with $g' \colon B' \to \operatorname{Spec} R'$ smooth, separated, locally of finite type and quasi-compact, a relative group law $LB'$ on $g'$, and a morphism $jY'$ from $X' \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ (that is, $\operatorname{pullback.snd}\,(X'.\iota \gg f)\,s$) to $B'$ over $\operatorname{Spec} R'$ whose underlying morphism is an open immersion. Its image is constrained by `hjY'₁`, every $b \in B'$ with $g'(b)$ not the closed point of $R'$ lies in the range of $jY'$, and `hjY'₂`, every $b \in B'$ with $g'(b)$ the closed point of $R'$ such that every $y$ specialising to $b$ with $g'(y)$ the closed point equals $b$ (that is, every maximal point of the special fibre) lies in the range of $jY'$. The hypothesis `hres'` states that $jY'$ carries $m$ into the law $LB'$: for every scheme $T$, every $t' \colon T \to \operatorname{Spec} R'$, every point $w$ of $U$ over $t' \circ s$ and all points $a, b, c$ of $X'$ over $t' \circ s$ such that $a$ followed by $X'.\iota$ is $w$ followed by $U.\iota$ and $\operatorname{pullback.fst} f f$, $b$ followed by $X'.\iota$ is $w$ followed by $U.\iota$ and $\operatorname{pullback.snd} f f$, and $c$ followed by $X'.\iota$ is $w$ followed by the inclusion $U \le W$ and $m$, the base change of $c$ along $s$ followed by $jY'$ equals $LB'.\mathrm{mul}$ of the base changes of $a$ and of $b$ followed by $jY'$.
--
--   Finally there is a descent action $A$ of $s$ on $g'$, that is (by the definition of `DescentAction`) a morphism $A.\mathrm{act} \colon (B' \times_{\operatorname{Spec} R} \operatorname{Spec} R') \to B'$, formed as the pullback of $g' \circ s$ and $s$, satisfying $A.\mathrm{act}$ followed by $g'$ equals the second projection, the unit identity $\mathrm{unitMap} \gg A.\mathrm{act} = \mathbb{1}$, and the transitivity identity relating $\mathrm{actMap}$ and the $(1,3)$-projection. Two compatibilities are assumed. `hA₁`: the open immersion $jY'$ is equivariant, namely the pullback comparison morphism induced by $jY'.1$ and the identities, followed by $A.\mathrm{act}$, equals the act of the canonical descent action `DescentAction.canonical s (X'.ι ≫ f)` on $X' \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ followed by $jY'.1$. `hA₂`: the action is a homomorphism for $LB'$, namely for every scheme $T$, all $\tau, t' \colon T \to \operatorname{Spec} R'$ with $t' \circ s = \tau \circ s$ and all points $x, y$ of $B'$ over $t'$, the base change along $s$ of $LB'.\mathrm{mul}\,t'\,x\,y$, composed with the point $\langle A.\mathrm{act}, A.\mathrm{act\_comp}\rangle$ of $B'$, equals $LB'.\mathrm{mul}\,\tau$ of the corresponding composites formed from $x$ and from $y$. The last hypothesis `hA` is that $A$ is effective: there exist a scheme $Z$ over $\operatorname{Spec} R$ with structure morphism $h$, an isomorphism $Z \times_{\operatorname{Spec} R} \operatorname{Spec} R' \cong B'$ over $\operatorname{Spec} R'$, and the identity matching the transported $A.\mathrm{act}$ with the canonical action on $Z$.
--
--   Conclusion. There exist a scheme $B$, a morphism $g \colon B \to \operatorname{Spec} R$, a relative group law $LB$ on $g$, a morphism $jY \colon X' \to B$ over $\operatorname{Spec} R$ and a morphism $e'$ from the generic fibre of $g$ to $XK$ over $\operatorname{Spec} K$ such that: $g$ is smooth; $g$ is separated; $g$ is locally of finite type; $g$ is quasi-compact; the underlying morphism of $jY$ is an open immersion; every $b \in B$ with $g(b)$ not the closed point of $R$ lies in the range of $jY$; every $b \in B$ with $g(b)$ the closed point of $R$ such that every $y$ specialising to $b$ with $g(y)$ the closed point equals $b$ lies in the range of $jY$; the underlying morphism of $e'$ is an isomorphism; $e'$ is a homomorphism of group laws on generic fibres, namely for every scheme $T$, every $t \colon T \to \operatorname{Spec} K$ and all points $x, y$ of the generic fibre of $g$ over $t$, the composite of $(LB.\mathrm{genericFibre}\,K).\mathrm{mul}\,t\,x\,y$ with $e'$ equals $LXK.\mathrm{mul}\,t$ of the composites of $x$ and of $y$ with $e'$; the generic-fibre restriction of $jY$ followed by $e'$ equals the generic-fibre restriction of the open immersion $X' \hookrightarrow X$ followed by $e$; and $LB$ restricts to $m$ on $U$, namely for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$, every point $w$ of $U$ over $t$ and all points $a, b, c$ of $X'$ over $t$ with $a$ followed by $X'.\iota$ equal to $w$ followed by $U.\iota$ and $\operatorname{pullback.fst} f f$, $b$ followed by $X'.\iota$ equal to $w$ followed by $U.\iota$ and $\operatorname{pullback.snd} f f$, and $c$ followed by $X'.\iota$ equal to $w$ followed by the inclusion $U \le W$ and $m$, the composite of $c$ with $jY$ equals $LB.\mathrm{mul}\,t$ of the composites of $a$ and of $b$ with $jY$.
--
--   This is the descent step in the construction of a group scheme from a birational group law over a discrete valuation ring (Bosch–Lütkebohmert–Raynaud, Néron Models, 6.5): once a solution $B'$ of the law has been produced over a finite étale faithfully flat extension $R'$ together with an effective descent datum compatible with the law and with the open immersion of $X'$, the scheme effecting the datum is a solution over $R$ with the same properties, its separatedness coming from descent of `IsSeparated` along surjective flat quasi-compact morphisms ([`AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact`](thm.html#AlgebraicGeometry.IsSeparated.descendsAlong_surjective_inf_flat_inf_quasiCompact)). It is used by [`NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing), in the line of results producing Néron models and good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_DescentAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
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
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b) jY'))
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g')
    (hA₁ :
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫ jY'.1)
    (hA₂ : ∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
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
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g')))
    (hA : A.Effective) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp c jY =
          LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY)) := by sorry
