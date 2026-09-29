-- Prove2me | Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
-- name    : NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/2d65917a-774f-55d8-a0b8-6e0243662063
-- title:
--   Finite étale descent of a birational group law solution
-- statement:
--   Throughout, $R$ is a discrete valuation ring (a domain) which is in addition a henselian local ring, and $K$ is a field which is an $R$-algebra and a fraction field of $R$. On the generic side there are a scheme $XK$, a morphism $gK \colon XK \to \operatorname{Spec} K$ and a structure `LXK : RelativeGroupLaw K gK`, that is, a functorial group law on the $T$-points of $gK$: operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on the sets $\{\varphi : T \to XK \mid \varphi \circ gK = t\}$ for each $t \colon T \to \operatorname{Spec} K$, satisfying associativity, the unit laws, left inverse, and naturality in $T$.
--
--   On the integral side there is $f \colon X \to \operatorname{Spec} R$, assumed smooth, separated, locally of finite type and quasi-compact, with the hypothesis `hXk` that some point of $X$ maps to the closed point of $R$. A morphism $e$ from the generic fibre $X_K = X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (presented as the second projection of the pullback of $f$ along $\operatorname{Spec}$ of the structure map $R \to K$) to $XK$ over $\operatorname{Spec} K$ is given, with $e$ an isomorphism.
--
--   The birational group law data consist of an open subscheme $W$ of $X \times_{\operatorname{Spec} R} X$ and a morphism $m \colon W \to X$ over $\operatorname{Spec} R$, the structure morphism of $W$ being the one induced by the first projection. Two hypotheses locate $W$: `hW₁` says that every point $p$ of $X \times_R X$ whose image under $\mathrm{pr}_1$ followed by $f$ is not the closed point of $R$ lies in $W$ (so $W$ contains the generic fibre), and `hW₂` says that every point $p$ lying over the closed point which is maximal in the special fibre — in the sense that any $y$ with $p \in \overline{\{y\}}$ and $y$ over the closed point equals $p$ — lies in $W$. The hypothesis `hmK` expresses that $m$ induces on generic fibres the multiplication of `LXK` transported through $e$: the generic fibre restriction of $m$ followed by $e$ equals the canonical morphism $W_K \to (X \times_R X)_K$ followed by the underlying morphism of $\mathrm{mul}$ of `LXK` applied to the two generic fibre restrictions of $\mathrm{pr}_1$ and $\mathrm{pr}_2$ transported through $e$.
--
--   Four further hypotheses concern the two morphisms $\Phi = (\mathrm{pr}_1 \circ \iota_W, m)$ and $\Psi = (m, \mathrm{pr}_2 \circ \iota_W)$ from $W$ to $X \times_R X$ obtained by the universal property of the pullback: `hΦ` and `hΨ` assert that $\Phi$ and $\Psi$ are open immersions, while `hΦ₂` and `hΨ₂` assert that every point of $X \times_R X$ maximal in the special fibre (in the sense just described) lies in the set-theoretic image of $\Phi$, respectively of $\Psi$.
--
--   Next, an open subscheme $X' \subseteq X$ and an open subscheme $U \subseteq X \times_R X$ with $U \le W$ (`hUW`) are given, subject to the following conditions. `hX'₁`: $X'$ contains every point of $X$ not lying over the closed point of $R$; `hX'₂`: $X'$ contains every point of $X$ over the closed point that is maximal in the special fibre. `hU₁`: $U$ contains every point of $X \times_R X$ not lying over the closed point. `hU₂`: for every $q \in U$, the points $\mathrm{pr}_1(q)$, $\mathrm{pr}_2(q)$ and $m(q)$ all lie in $X'$. `hU₃` is a conjunction of six density clauses, required for every $x \in X'$: inside the subspace $\{q \in X \times_R X \mid \mathrm{pr}_1(q) = x\}$ the preimages of $U$, of the image under $\Phi$ of $\{w \in W \mid \iota_W(w) \in U\}$, and of the image under $\Psi$ of the same set are dense; and the three analogous preimages are dense in the subspace $\{q \in X \times_R X \mid \mathrm{pr}_2(q) = x\}$.
--
--   Finally, the descent datum. $R'$ is a discrete valuation ring (a domain) which is an $R$-algebra, finite as an $R$-module, étale over $R$ and faithfully flat over $R$. There are a scheme $B'$, a morphism $g' \colon B' \to \operatorname{Spec} R'$ which is smooth, separated, locally of finite type and quasi-compact, a structure `LB' : RelativeGroupLaw R' g'`, and a morphism $jY'$ over $\operatorname{Spec} R'$ from the base change $X' \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ (the second projection of the pullback of $\iota_{X'} \circ f$ along $\operatorname{Spec}$ of $R \to R'$) to $B'$, whose underlying morphism is an open immersion. Its image is controlled by `hjY'₁` (every point of $B'$ not over the closed point of $R'$ lies in the range of $jY'$) and `hjY'₂` (every point of $B'$ over the closed point of $R'$ that is maximal in the special fibre of $g'$ lies in that range). The hypothesis `hres'` says that `LB'` restricts to $m$ on $U$ after base change: for every scheme $T$, every $t' \colon T \to \operatorname{Spec} R'$, every $T$-point $w$ of $U$ over $t'$ followed by $\operatorname{Spec}$ of $R \to R'$, and all $T$-points $a, b, c$ of $X'$ over the same base morphism, if $a$ followed by $\iota_{X'}$ equals $w$ followed by $\iota_U$ and $\mathrm{pr}_1$, if $b$ followed by $\iota_{X'}$ equals $w$ followed by $\iota_U$ and $\mathrm{pr}_2$, and if $c$ followed by $\iota_{X'}$ equals $w$ followed by the inclusion $U \le W$ and $m$, then the $T$-point of $X' \times_R \operatorname{Spec} R'$ determined by $c$, composed with $jY'$, equals the $\mathrm{mul}$ of `LB'` at $t'$ applied to the corresponding composites coming from $a$ and $b$.
--
--   The conclusion asserts the existence of a scheme $B$, a morphism $g \colon B \to \operatorname{Spec} R$, a structure `LB : RelativeGroupLaw R g`, a morphism $jY \colon X' \to B$ over $\operatorname{Spec} R$ and a morphism $e'$ from the generic fibre $B_K$ (the second projection of the pullback of $g$ along $\operatorname{Spec}$ of $R \to K$) to $XK$ over $\operatorname{Spec} K$, such that, conjunct by conjunct: $g$ is smooth; $g$ is separated; $g$ is locally of finite type; $g$ is quasi-compact; the underlying morphism of $jY$ is an open immersion; every point $b$ of $B$ with $g(b)$ not the closed point of $R$ lies in the range of $jY$; every point $b$ of $B$ over the closed point of $R$ such that any $y$ with $b \in \overline{\{y\}}$ and $y$ over the closed point equals $b$ lies in the range of $jY$; the underlying morphism of $e'$ is an isomorphism; $e'$ is compatible with the group laws, in that for every scheme $T$, every $t \colon T \to \operatorname{Spec} K$ and all $T$-points $x, y$ of $B_K$ over $t$, composing the $\mathrm{mul}$ at $t$ of the generic fibre law `(LB.genericFibre K)` — the base change of `LB` along $\operatorname{Spec}$ of $R \to K$ — with $e'$ gives the $\mathrm{mul}$ of `LXK` at $t$ applied to $x$ followed by $e'$ and $y$ followed by $e'$; the identification $e'$ extends $e$, namely the generic fibre restriction of $jY$ followed by $e'$ equals the generic fibre restriction of the open immersion $\iota_{X'} \colon X' \to X$ followed by $e$; and finally `LB` restricts to $m$ on $U$ over $R$ itself: for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$, every $T$-point $w$ of $U$ over $t$ and all $T$-points $a, b, c$ of $X'$ over $t$ with $a$ followed by $\iota_{X'}$ equal to $w$ followed by $\iota_U$ and $\mathrm{pr}_1$, with $b$ followed by $\iota_{X'}$ equal to $w$ followed by $\iota_U$ and $\mathrm{pr}_2$, and with $c$ followed by $\iota_{X'}$ equal to $w$ followed by the inclusion $U \le W$ and $m$, one has that $c$ followed by $jY$ equals the $\mathrm{mul}$ of `LB` at $t$ applied to $a$ followed by $jY$ and $b$ followed by $jY$.
--
--   This is the finite étale descent step in the construction of a smooth separated group scheme over a henselian discrete valuation ring solving a given birational group law, as in Bosch–Lütkebohmert–Raynaud, Néron Models, 6.5: a solution over a finite étale faithfully flat extension $R'$, agreeing with the given law on $U$, is descended to a solution over $R$ together with an identification of its generic fibre with the given generic group law. It is used by [`NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing), and the proof cites the construction of the descent action, the existence of affine opens containing finite sets of points of a relative group law, effectivity of descent along finite étale faithfully flat extensions, henselianity of module-finite local extensions, and the corresponding statement for an effective descent action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ W)
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
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U})))
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
