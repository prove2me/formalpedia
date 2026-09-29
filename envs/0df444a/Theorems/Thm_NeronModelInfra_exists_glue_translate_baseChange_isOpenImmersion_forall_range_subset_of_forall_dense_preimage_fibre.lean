-- Prove2me | Theorems.Thm_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
-- name    : NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/2a273600-d177-5893-b11e-b19aa02285b1
-- title:
--   One glued translate over a faithfully flat extension
-- statement:
--   Throughout, $R$ is a discrete valuation ring (a domain with the `IsDiscreteValuationRing` property), $S=\operatorname{Spec} R$, and $y\colon Y\to S$ is a morphism of schemes which is smooth, separated, locally of finite type and quasi-compact. On the fibre product $Y\times_S Y$ (the Lean `pullback y y`) write $p_1,p_2$ for the two projections. The data consists of an open subscheme $U\le Y\times_S Y$, with open immersion $\iota_U$, and of a morphism $m\colon U\to Y$ over $S$, i.e. an element of `SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y`: a morphism $m_1\colon U\to Y$ together with the identity $m_1$ followed by $y$ equals $\iota_U$ followed by $p_1$ followed by $y$. For a point $x\in Y$ and $i\in\{1,2\}$, the phrase "$Z$ is dense in the $p_i$-fibre over $x$" abbreviates: the preimage of $Z\subseteq |Y\times_S Y|$ under the inclusion of the subtype $\{q\in |Y\times_S Y| : p_i(q)=x\}$, with its subspace topology, is dense. Put $\Phi=\langle \iota_U\,p_1,\;m_1\rangle$ and $\Psi=\langle m_1,\;\iota_U\,p_2\rangle$ for the two morphisms $U\to Y\times_S Y$ obtained by `pullback.lift` from these pairs of components.
--
--   The hypotheses on $(y,U,m)$ fall into four groups. (i) Chart density: `hU₁` and `hU₂` state that $U$ is dense in every $p_1$-fibre and in every $p_2$-fibre. (ii) Birationality: `hΦ` states that $\Phi$ is an open immersion, `hΦ₁`, `hΦ₂` that the set-theoretic image of $\Phi$ is dense in every $p_1$-fibre and in every $p_2$-fibre; `hΨ`, `hΨ₁`, `hΨ₂` are the same three assertions for $\Psi$. (iii) Associativity `hassoc`: for every scheme $T$, every $t\colon T\to S$ and all four $T$-points $u,v,p,q$ of $U$ over $t$ (elements of `SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)`), if $p_2(u)=p_1(v)$, $p_1(p)=m(u)$, $p_2(p)=p_2(v)$, $p_1(q)=p_1(u)$ and $p_2(q)=m(v)$ (all equalities of composites of the underlying morphisms), then $m(p)=m(q)$. (iv) Generic fibre `hUK`: every point $q$ of $Y\times_S Y$ whose image under $p_1$ followed by $y$ is not the closed point of $\operatorname{Spec} R$ lies in $U$.
--
--   Next, $R'$ is a discrete valuation ring which is an $R$-algebra, faithfully flat as an $R$-module, and $y'\colon Y'\to \operatorname{Spec} R'$ is smooth, separated, locally of finite type and quasi-compact. The comparison datum is $\iota$, an element of `SchemeHomOver (pullback.snd y (Spec.map (algebraMap R R'))) y'`, that is a morphism $\iota_1\colon Y\times_R \operatorname{Spec} R'\to Y'$ compatible with the structure morphisms to $\operatorname{Spec} R'$, assumed to be an open immersion. Two further hypotheses bound the part of $Y'$ missed by $\iota$: `hgen`, every $p\in Y'$ with $y'(p)$ different from the closed point of $\operatorname{Spec} R'$ lies in the range of $\iota_1$ on points; and `hmax`, every $p\in Y'$ which is maximal in its fibre for specialisation (the only $p'$ with $p'\rightsquigarrow p$ and $y'(p')=y'(p)$ being $p$ itself) lies in that range. On $Y'$ there is a second law: an open $U'\le Y'\times_{R'}Y'$ and a morphism $m'\colon U'\to Y'$ over $\operatorname{Spec} R'$, subject to `hU'₁`, `hU'₂` (chart density in all $p_1$- and $p_2$-fibres), `hΦ'`, `hΦ'₁`, `hΦ'₂`, `hΨ'`, `hΨ'₁`, `hΨ'₂` (the corresponding open-immersion and fibrewise density statements for the two morphisms $\langle \iota_{U'}p_1,m'_1\rangle$ and $\langle m'_1,\iota_{U'}p_2\rangle$) and `hassoc'` (associativity in the same six-premise form as `hassoc`); no analogue of `hUK` is assumed for $U'$. Finally `hext` says that $m'$ extends $m$ along $\iota$: for every scheme $T$, every $t'\colon T\to\operatorname{Spec} R'$, every $T$-point $w$ of $U$ over $t'$ followed by $\operatorname{Spec}(R\to R')$, and all $T$-points $a,b,c$ of $Y$ over that same base morphism (these three letters are bound inside the clause) with $a=p_1(w)$, $b=p_2(w)$, $c=m(w)$, there is a $T$-point $w'$ of $U'$ over $t'$ such that $p_1(w')$, $p_2(w')$ and $m'(w')$ are, respectively, the base-changed points `RelativeGroupLaw.baseChangePointOfBase` of $a$, $b$, $c$ — the $T$-points of $Y\times_R\operatorname{Spec} R'$ obtained by `pullback.lift` from the given point and $t'$ — each followed by $\iota_1$.
--
--   The next level is given by a discrete valuation ring $R''$ which is an $R'$-algebra, faithfully flat as an $R'$-module, and an $R$-algebra with $R\to R'\to R''$ a scalar tower, together with a section $a\colon \operatorname{Spec} R''\to Y$ over the base, meaning `ha`: $a$ followed by $y$ equals $\operatorname{Spec}(R\to R'')$.
--
--   The conclusion asserts the existence of a scheme $Y''$, a morphism $y''\colon Y''\to\operatorname{Spec} R''$, a morphism $\iota_2\colon Y\times_R\operatorname{Spec} R''\to Y''$ over $\operatorname{Spec} R''$ (an element of `SchemeHomOver (pullback.snd y (Spec.map (algebraMap R R''))) y''`), an open $U''\le Y''\times_{R''}Y''$ and a morphism $m''\colon U''\to Y''$ over $\operatorname{Spec} R''$, such that the following hold, in this order: $y''$ is smooth, separated, locally of finite type and quasi-compact; $\iota_2$ is an open immersion; every $p\in Y''$ with $y''(p)$ not the closed point of $\operatorname{Spec} R''$ lies in the range of $\iota_2$ on points; every $p\in Y''$ maximal in its fibre for specialisation (in the sense used for `hmax`) lies in that range; $U''$ is dense in every $p_1$-fibre and in every $p_2$-fibre of $Y''\times_{R''}Y''$; $\langle \iota_{U''}p_1,m''_1\rangle$ is an open immersion and its image is dense in every $p_1$-fibre and in every $p_2$-fibre; $\langle m''_1,\iota_{U''}p_2\rangle$ is an open immersion and its image is dense in every $p_1$-fibre and in every $p_2$-fibre; $(U'',m'')$ satisfies associativity in the same six-premise form as `hassoc`, for all $T$-points over all $t\colon T\to\operatorname{Spec} R''$; $m''$ extends $m$ along $\iota_2$, that is, the exact analogue of `hext` holds with $R'$, $\iota$, $U'$, $m'$ replaced by $R''$, $\iota_2$, $U''$, $m''$ and with the base change taken along $\operatorname{Spec}(R\to R'')$.
--
--   Three further conjuncts conclude the statement. First, $y''$ admits a section: there is $a''\colon\operatorname{Spec} R''\to Y''$ with $a''$ followed by $y''$ the identity. Secondly, there is a morphism $j\colon Y'\times_{R'}\operatorname{Spec} R''\to Y''$ which is an open immersion, satisfies $j$ followed by $y''$ equals the second projection, and is compatible with $\iota$ and $\iota_2$ in the following pointwise sense: for every scheme $T$ and morphisms $x\colon T\to Y\times_R\operatorname{Spec} R''$, $x_1\colon T\to Y\times_R\operatorname{Spec} R'$ and $x_2\colon T\to Y'\times_{R'}\operatorname{Spec} R''$ such that $x_1$ followed by the first projection equals $x$ followed by the first projection, $x_1$ followed by the second projection equals $x$ followed by the second projection and then $\operatorname{Spec}(R'\to R'')$, $x_2$ followed by the first projection equals $x_1$ followed by $\iota_1$, and $x_2$ followed by the second projection equals $x$ followed by the second projection, one has that $x_2$ followed by $j$ equals $x$ followed by $\iota_2$. Thirdly, the law $m''$ extends over the translate slice determined by $a$: there are an open $D$ of $Y''\times_{R''}Y''$ with $U''\le D$ and a morphism $M\colon D\to Y''$ over $\operatorname{Spec} R''$ whose restriction along the inclusion $U''\le D$ is $m''_1$, with the property that for every $a_2\colon\operatorname{Spec} R''\to Y\times_R\operatorname{Spec} R''$ whose composites with the two projections are $a$ and the identity, and for every scheme $T$ and morphisms $b\colon T\to Y\times_R\operatorname{Spec} R''$ and $q\colon T\to Y''\times_{R''}Y''$ such that $q$ followed by $p_1$ equals $b$ followed by the second projection, then $a_2$, then $\iota_2$, while $q$ followed by $p_2$ equals $b$ followed by $\iota_2$, the set-theoretic image of $q$ is contained in $D$.
--
--   This is the inductive step, over a tower of faithfully flat extensions of discrete valuation rings, in the passage from a strict birational group law to a group scheme: starting from a smooth separated quasi-compact $Y$ over $R$ carrying a generically associative partial law $m$ defined on a fibrewise dense open $U$ containing the generic fibre, together with an enlargement $Y'$ of $Y\times_R R'$ carrying a compatible law, it produces at the next level $R''$ an enlargement $Y''$ of $Y\times_R R''$ (indeed containing $Y'\times_{R'}R''$ as an open subscheme) with its own partial law, a section of $y''$, and an open domain $D\supseteq U''$ on which the law is defined along the whole slice through the point determined by the given $R''$-point $a$ of $Y$ — the gluing of one left translate. It is used by [`NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing); note that, unlike the classical formulation, the ring extensions here are only assumed to be faithfully flat extensions of discrete valuation rings, with no finiteness or étaleness requirement.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    [Smooth y] [IsSeparated y] [LocallyOfFiniteType y] [QuasiCompact y]
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
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y') [IsOpenImmersion ι.1]
    (hgen : ∀ p : Y', y'.base p ≠ IsLocalRing.closedPoint R' → p ∈ Set.range ι.1.base)
    (hmax : ∀ p : Y', (∀ p' : Y', p' ⤳ p → y'.base p' = y'.base p → p' = p) → p ∈ Set.range ι.1.base)
    (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y')
    (hU'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hU'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U' : Set ↑(pullback y' y'))))
    (hΦ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)))
    (hΦ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΦ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U'.ι ≫ pullback.fst y' y') m'.1
            ((Category.assoc _ _ _).trans m'.2.symm)).base)))
    (hΨ' : IsOpenImmersion
      (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ'₁ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hΨ'₂ : ∀ x : Y',
      Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m'.1 (U'.ι ≫ pullback.snd y' y')
            (m'.2.trans (by rw [Category.assoc, pullback.condition]))).base)))
    (hassoc' : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
        (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
      u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
      p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 → p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
      q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' → q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
      p.1 ≫ m'.1 = q.1 ≫ m'.1)
    (hext : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
      a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
      ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
        w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
        w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
        w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1)
    (R'' : Type u) [CommRing R''] [IsDomain R''] [IsDiscreteValuationRing R''] [Algebra R' R'']
    [Module.FaithfullyFlat R' R''] [Algebra R R''] [IsScalarTower R R' R'']
    (a : Spec (CommRingCat.of R'') ⟶ Y) (ha : a ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R R''))) :
    ∃ (Y'' : Scheme.{u}) (y'' : Y'' ⟶ Spec (CommRingCat.of R''))
      (ι₂ : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y'')
      (U'' : (pullback y'' y'').Opens) (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
      Smooth y'' ∧ IsSeparated y'' ∧ LocallyOfFiniteType y'' ∧ QuasiCompact y'' ∧
      IsOpenImmersion ι₂.1 ∧
      (∀ p : Y'', y''.base p ≠ IsLocalRing.closedPoint R'' → p ∈ Set.range ι₂.1.base) ∧
      (∀ p : Y'', (∀ p' : Y'', p' ⤳ p → y''.base p' = y''.base p → p' = p) → p ∈ Set.range ι₂.1.base) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (U'' : Set ↑(pullback y'' y'')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') (U''.ι ≫ pullback.fst y'' y'') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.fst y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y'' y'') // (pullback.snd y'' y'').base q = x} → ↑(pullback y'' y'')) ⁻¹'
          (Set.range (pullback.lift (f := y'') (g := y'') m''.1 (U''.ι ≫ pullback.snd y'' y'')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R''))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y'' y'' ≫ y'')),
        u.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        p.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ U''.ι ≫ pullback.snd y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.fst y'' y'' = u.1 ≫ U''.ι ≫ pullback.fst y'' y'' →
        q.1 ≫ U''.ι ≫ pullback.snd y'' y'' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R''))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (U.ι ≫ pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U''.ι ≫ pullback.fst y'' y'' ≫ y''),
          w'.1 ≫ U''.ι ≫ pullback.fst y'' y'' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) a).1 ≫ ι₂.1 ∧
          w'.1 ≫ U''.ι ≫ pullback.snd y'' y'' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) b).1 ≫ ι₂.1 ∧
          w'.1 ≫ m''.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R''))) c).1 ≫ ι₂.1) ∧
      (∃ a'' : Spec (CommRingCat.of R'') ⟶ Y'', a'' ≫ y'' = 𝟙 _) ∧
      (∃ j : pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ⟶ Y'',
        IsOpenImmersion j ∧ j ≫ y'' = pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ∧
        ∀ {T : Scheme.{u}} (x : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R''))))
          (x₁ : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (x₂ : T ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R'')))),
          x₁ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₁ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ Spec.map (CommRingCat.ofHom (algebraMap R' R'')) →
          x₂ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x₁ ≫ ι.1 →
          x₂ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = x ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) →
          x₂ ≫ j = x ≫ ι₂.1) ∧
      (∃ (D : (pullback y'' y'').Opens) (hle : U'' ≤ D)
        (M : SchemeHomOver (D.ι ≫ pullback.fst y'' y'' ≫ y'') y''),
        (pullback y'' y'').homOfLE hle ≫ M.1 = m''.1 ∧
        ∀ (a₂ : Spec (CommRingCat.of R'') ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))),
          a₂ ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = a → a₂ ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) = 𝟙 _ →
          ∀ {T : Scheme.{u}} (b : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R'')))) (q : T ⟶ pullback y'' y''),
            q ≫ pullback.fst y'' y'' = b ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R''))) ≫ a₂ ≫ ι₂.1 →
            q ≫ pullback.snd y'' y'' = b ≫ ι₂.1 →
            Set.range q.base ⊆ (D : Set ↑(pullback y'' y''))) := by sorry
