-- Prove2me | Theorems.Thm_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- name    : NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3a735e2b-f3ee-5d30-b0ec-2e5b90ecbed0
-- title:
--   Finite étale solution of a strict birational group law
-- statement:
--   Throughout, $R$ is a discrete valuation ring that is a domain and a henselian local ring, and $K$ is a field equipped with an $R$-algebra structure making it the fraction field of $R$. Fixed data: a $K$-scheme $g_K\colon X_K \to \operatorname{Spec} K$ together with a relative group law `LXK` on it, i.e. functorial multiplication, unit and inverse operations on $T$-points over $\operatorname{Spec} K$ satisfying associativity, the two unit laws, left inversion and naturality in $T$; a morphism $f\colon X \to \operatorname{Spec} R$ which is smooth, separated, locally of finite type and quasi-compact; the hypothesis `hXk` that some point of $X$ lies over the closed point of $R$; and a morphism $e$ from the generic fibre $\operatorname{pr}_2\colon X \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ (the pullback of $f$ along $\operatorname{Spec}$ of $R \to K$) to $g_K$ over $\operatorname{Spec} K$, whose underlying morphism of schemes is an isomorphism.
--
--   The law is given by an open subscheme $W \subseteq X \times_{\operatorname{Spec} R} X$ and a morphism $m\colon W \to X$ over $\operatorname{Spec} R$, that is, an element $m$ of the type of morphisms $W \to X$ commuting with $W \hookrightarrow X\times_R X \xrightarrow{\operatorname{pr}_1} X \xrightarrow{f} \operatorname{Spec} R$ and $f$. The hypotheses on $W$ are: `hW₁`, every point of $X\times_R X$ whose image under $\operatorname{pr}_1$ followed by $f$ is not the closed point of $R$ lies in $W$; and `hW₂`, every point $p$ over the closed point which is maximal there, in the sense that any $y$ with $y \rightsquigarrow p$ lying over the closed point equals $p$, lies in $W$. The hypothesis `hmK` states that $m$ induces the group law on generic fibres: the generic fibre restriction of $m$ (the morphism $W \times_R \operatorname{Spec} K \to X\times_R\operatorname{Spec} K$ induced by $m$) followed by $e$ equals the canonical morphism $W\times_R\operatorname{Spec} K \to (X\times_R X)\times_R \operatorname{Spec} K$ induced by $W \hookrightarrow X \times_R X$ and the identity on $\operatorname{Spec} K$, followed by the underlying morphism of `LXK.mul` applied to the two $((X\times_R X)\times_R\operatorname{Spec} K)$-points of $X_K$ obtained from the generic fibre restrictions of $\operatorname{pr}_1$ and of $\operatorname{pr}_2$ composed with $e$.
--
--   The translations are constrained by four hypotheses. `hΦ`: the morphism $\Phi = (W\hookrightarrow X\times_R X \xrightarrow{\operatorname{pr}_1} X,\; m)\colon W \to X\times_R X$ is an open immersion; `hΦ₂`: every point $p$ of $X\times_R X$ lying over the closed point of $R$ (via $\operatorname{pr}_1$ followed by $f$) and maximal among such points in the sense of `hW₂` lies in the set-theoretic image of $\Phi$. `hΨ` and `hΨ₂` are the same two assertions for $\Psi = (m,\; W\hookrightarrow X\times_R X \xrightarrow{\operatorname{pr}_2} X)\colon W \to X\times_R X$.
--
--   Finally there are an open subscheme $X' \subseteq X$ and an open subscheme $U \subseteq X\times_R X$ with $U \le W$ (`hUW`), subject to: `hX'₁`, every point of $X$ not over the closed point of $R$ lies in $X'$; `hX'₂`, every point $x$ of $X$ over the closed point which is maximal there (any $y \rightsquigarrow x$ over the closed point equals $x$) lies in $X'$; `hU₁`, every point of $X\times_R X$ not over the closed point lies in $U$; `hU₂`, for every $q \in U$ the three points $\operatorname{pr}_1(q)$, $\operatorname{pr}_2(q)$ and $m(q)$ lie in $X'$; and `hU₃`, which for every $x \in X'$ asserts six density statements (summarised here): each of the three subsets $U$, the image of $\{w \in W : W \hookrightarrow X\times_R X \text{ sends } w \text{ into } U\}$ under $\Phi$, and the corresponding image under $\Psi$, has dense preimage in the subspace of points $q$ of $X \times_R X$ with $\operatorname{pr}_1(q) = x$, and likewise in the subspace of points $q$ with $\operatorname{pr}_2(q) = x$.
--
--   Under these hypotheses there exist: a type $R'$ with a commutative ring structure making it a domain and a discrete valuation ring, an $R$-algebra structure on $R'$ which is module-finite, étale and faithfully flat; a scheme $Y'$ with a morphism $y'\colon Y' \to \operatorname{Spec} R'$; a morphism $\iota$ from the base change $X' \times_{\operatorname{Spec} R} \operatorname{Spec} R'$ (the pullback of $X' \hookrightarrow X \xrightarrow{f} \operatorname{Spec} R$ along $\operatorname{Spec}$ of $R \to R'$, with its structural projection to $\operatorname{Spec} R'$) to $Y'$ over $\operatorname{Spec} R'$; an open subscheme $U' \subseteq Y'\times_{\operatorname{Spec} R'} Y'$; and a morphism $m'\colon U' \to Y'$ over $\operatorname{Spec} R'$, such that all of the following hold.
--
--   (i) $y'$ is smooth, separated, locally of finite type and quasi-compact. (ii) The underlying morphism of $\iota$ is an open immersion. (iii) Every point $p$ of $Y'$ with $y'(p)$ different from the closed point of $R'$ lies in the image of $\iota$. (iv) Every point $p$ of $Y'$ such that every $p'$ with $p' \rightsquigarrow p$ and $y'(p') = y'(p)$ equals $p$ lies in the image of $\iota$. (v) For every point $x$ of $Y'$, $U'$ has dense preimage in the subspace of points $q$ of $Y'\times_{R'} Y'$ with $\operatorname{pr}_1(q) = x$; (vi) the same with $\operatorname{pr}_2$ in place of $\operatorname{pr}_1$. (vii) $\Phi' = (U'\hookrightarrow Y'\times_{R'}Y' \xrightarrow{\operatorname{pr}_1} Y',\; m')\colon U' \to Y'\times_{R'}Y'$ is an open immersion; (viii) and (ix) for every point $x$ of $Y'$ the image of $\Phi'$ has dense preimage in the subspace of points with $\operatorname{pr}_1(q) = x$, and in the subspace of points with $\operatorname{pr}_2(q) = x$. (x) $\Psi' = (m',\; U'\hookrightarrow Y'\times_{R'}Y' \xrightarrow{\operatorname{pr}_2} Y')$ is an open immersion; (xi) and (xii) the image of $\Psi'$ satisfies the same two density conditions.
--
--   (xiii) An associativity condition for $m'$ on points: for every scheme $T$, every $t\colon T \to \operatorname{Spec} R'$ and all $T$-points $u, v, p, q$ of $U'$ over $t$ (elements of the type of morphisms $T \to U'$ commuting with $U'\hookrightarrow Y'\times_{R'}Y'\xrightarrow{\operatorname{pr}_1} Y' \xrightarrow{y'} \operatorname{Spec} R'$ and $t$), if the second component of $u$ equals the first component of $v$, if the first component of $p$ is $u$ followed by $m'$ and the second component of $p$ equals the second component of $v$, and if the first component of $q$ equals the first component of $u$ while the second component of $q$ is $v$ followed by $m'$, then $p$ followed by $m'$ equals $q$ followed by $m'$.
--
--   (xiv) Compatibility of $m'$ with $m$ after base change: for every scheme $T$, every $t'\colon T \to \operatorname{Spec} R'$, every $T$-point $w$ of $U$ over $t'$ followed by $\operatorname{Spec}$ of $R \to R'$, and all $T$-points $a, b, c$ of $X'$ over the same base morphism, if $a$ followed by $X' \hookrightarrow X$ is $w$ followed by $U \hookrightarrow X\times_R X \xrightarrow{\operatorname{pr}_1} X$, if $b$ followed by $X' \hookrightarrow X$ is $w$ followed by $U \hookrightarrow X \times_R X \xrightarrow{\operatorname{pr}_2} X$, and if $c$ followed by $X'\hookrightarrow X$ is $w$ followed by the inclusion $U \subseteq W$ and then $m$, then there exists a $T$-point $w'$ of $U'$ over $t'$ whose first component is the induced $T$-point of $X'\times_R \operatorname{Spec} R'$ determined by $a$ and $t'$ followed by $\iota$, whose second component is the corresponding point determined by $b$ followed by $\iota$, and with $w'$ followed by $m'$ equal to the point determined by $c$ followed by $\iota$.
--
--   (xv) $y'$ admits a section: there is $a'\colon \operatorname{Spec} R' \to Y'$ with $a'$ followed by $y'$ the identity. (xvi) Every point $q$ of $Y'\times_{R'}Y'$ with both $\operatorname{pr}_1(q)$ and $\operatorname{pr}_2(q)$ in the image of $\iota$ lies in $U'$.
--
--   This is the covering step of the theorem of Weil and Artin that a strict birational group law comes from a group scheme, in the form valid after a finite étale extension of a henselian discrete valuation ring: the birational law $(W,m)$ on $X$, strict on the open subscheme $X'$, is transported to a law $(U',m')$ defined on a dense open part of the square of a smooth separated $R'$-scheme $Y'$ into which the base change of $X'$ embeds as an open subscheme meeting the generic fibre and the maximal points of the special fibre. It is used in the construction of a group scheme from the birational group law on a smooth model, and is cited by [`NeronModelInfra.exists_finite_etale_relativeGroupLaw_isOpenImmersion_of_forall_dense_preimage_fibre_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_finite_etale_relativeGroupLaw_isOpenImmersion_of_forall_dense_preimage_fibre_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing
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
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
      (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
      Smooth y' ∧ IsSeparated y' ∧ LocallyOfFiniteType y' ∧ QuasiCompact y' ∧
      IsOpenImmersion ι.1 ∧
      (∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base) ∧
      (∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst f f ≫ f))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ q : ↑(pullback y' y'), (pullback.fst y' y').base q ∈ Set.range ι.1.base →
        (pullback.snd y' y').base q ∈ Set.range ι.1.base → q ∈ U') := by sorry
