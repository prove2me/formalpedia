-- Prove2me | Theorems.Thm_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- name    : NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/f30feda1-8978-5eac-80e1-59833ad96f9f
-- title:
--   Finite étale extension gluing translates of a birational group law
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain and a henselian local ring, and let $y \colon Y \to \operatorname{Spec} R$ be a morphism of schemes that is smooth, separated, locally of finite type and quasi-compact. Let $U$ be an open subscheme of the fibre product $Y \times_R Y$ (the categorical pullback of $y$ along itself), with inclusion $U.\iota$, and let $m$ be an element of `SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y`, that is, a morphism $m \colon U \to Y$ with $m \circ U.\iota =$ (the structure morphism of $U$ obtained as $U.\iota$ followed by $\mathrm{pr}_1$ followed by $y$); equivalently, $m$ is a morphism over $\operatorname{Spec} R$. Write $\Phi$ for the morphism $U \to Y \times_R Y$ with components $U.\iota$ followed by $\mathrm{pr}_1$, and $m$, and $\Psi$ for the morphism $U \to Y \times_R Y$ with components $m$, and $U.\iota$ followed by $\mathrm{pr}_2$ (both obtained by `pullback.lift`).
--
--   The hypotheses are as follows. Density of $U$ in the fibres (`hU₁`, `hU₂`): for every point $x$ of $Y$, the preimage of the underlying set of $U$ under the inclusion of the subspace $\{q \in Y \times_R Y : \mathrm{pr}_1(q) = x\}$ is dense in that subspace, and likewise for $\{q : \mathrm{pr}_2(q) = x\}$. Openness and density for the two universal translations (`hΦ`, `hΦ₁`, `hΦ₂`, `hΨ`, `hΨ₁`, `hΨ₂`): $\Phi$ is an open immersion and, for every point $x$ of $Y$, the preimage of the range of the underlying map of $\Phi$ is dense in each of the two subspaces $\{q : \mathrm{pr}_1(q) = x\}$ and $\{q : \mathrm{pr}_2(q) = x\}$; the same four conditions are imposed on $\Psi$. Associativity (`hassoc`): for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and all $T$-points $u, v, p, q$ of $U$ over $t$ (elements of `SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)`), if the second component of $u$ equals the first component of $v$, if the first component of $p$ is $m \circ u$ and its second component is the second component of $v$, and if the first component of $q$ is the first component of $u$ and its second component is $m \circ v$, then $m \circ p = m \circ q$. Non-empty special fibre (`hYk`): there is a point $x$ of $Y$ with $y(x)$ the closed point of $\operatorname{Spec} R$. Generic fibre contained in $U$ (`hUK`): every point $q$ of $Y \times_R Y$ whose image under $\mathrm{pr}_1$ followed by $y$ is not the closed point of $\operatorname{Spec} R$ lies in $U$.
--
--   The conclusion asserts the existence of a type $R'$ carrying a commutative ring structure, which is a domain and a discrete valuation ring, together with an $R$-algebra structure making $R'$ a finite, étale and faithfully flat $R$-algebra; a scheme $Y'$ and a morphism $y' \colon Y' \to \operatorname{Spec} R'$; a morphism $\iota$ in `SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y'`, i.e. a morphism $\iota \colon Y \times_R \operatorname{Spec} R' \to Y'$ over $\operatorname{Spec} R'$; an open subscheme $U'$ of $Y' \times_{R'} Y'$; and $m'$ in `SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'`, i.e. a morphism $m' \colon U' \to Y'$ over $\operatorname{Spec} R'$, such that the following hold, with $\Phi'$ and $\Psi'$ denoting the morphisms $U' \to Y' \times_{R'} Y'$ with components ($U'.\iota$ followed by $\mathrm{pr}_1$, $m'$) and ($m'$, $U'.\iota$ followed by $\mathrm{pr}_2$) respectively.
--
--   (i) $y'$ is smooth, separated, locally of finite type and quasi-compact. (ii) $\iota$ is an open immersion. (iii) Every point $p$ of $Y'$ with $y'(p)$ different from the closed point of $\operatorname{Spec} R'$ lies in the range of the underlying map of $\iota$. (iv) Every point $p$ of $Y'$ such that every point $p'$ of $Y'$ which specialises to $p$ and satisfies $y'(p') = y'(p)$ equals $p$ — that is, every maximal point of a fibre of $y'$ — lies in the range of the underlying map of $\iota$. (v) and (vi) For every point $x$ of $Y'$, the preimage of $U'$ is dense in the subspace $\{q \in Y' \times_{R'} Y' : \mathrm{pr}_1(q) = x\}$, and also in $\{q : \mathrm{pr}_2(q) = x\}$. (vii) $\Phi'$ is an open immersion, and (viii), (ix) for every point $x$ of $Y'$ the preimage of the range of its underlying map is dense in $\{q : \mathrm{pr}_1(q) = x\}$ and in $\{q : \mathrm{pr}_2(q) = x\}$. (x) $\Psi'$ is an open immersion, and (xi), (xii) the corresponding two density statements hold for the range of its underlying map. (xiii) $m'$ satisfies the associativity condition in exactly the shape of `hassoc`: for every scheme $T$, every $t \colon T \to \operatorname{Spec} R'$ and all $T$-points $u, v, p, q$ of $U'$ over $t$, if the second component of $u$ equals the first component of $v$, the first component of $p$ is $m' \circ u$ and its second component is the second component of $v$, and the first component of $q$ is the first component of $u$ and its second component is $m' \circ v$, then $m' \circ p = m' \circ q$.
--
--   (xiv) $m'$ extends $m$ after base change: for every scheme $T$, every $t' \colon T \to \operatorname{Spec} R'$, every $T$-point $w$ of $U$ over $t'$ followed by $\operatorname{Spec}$ of $R \to R'$, and all $T$-points $a, b, c$ of $Y$ over that same composite, if $a$ is $w$ followed by $U.\iota$ and $\mathrm{pr}_1$, $b$ is $w$ followed by $U.\iota$ and $\mathrm{pr}_2$, and $c = m \circ w$, then there is a $T$-point $w'$ of $U'$ over $t'$ whose first component equals the base change of $a$ (the point `RelativeGroupLaw.baseChangePointOfBase` of $Y \times_R \operatorname{Spec} R'$ determined by $a$ and $t'$) followed by $\iota$, whose second component equals the base change of $b$ followed by $\iota$, and with $m' \circ w'$ equal to the base change of $c$ followed by $\iota$.
--
--   (xv) $y'$ admits a section: there is $a' \colon \operatorname{Spec} R' \to Y'$ with $a'$ followed by $y'$ the identity. (xvi) Left translations by points over further finite étale extensions become everywhere defined on $Y'$: for every type $R''$ with a commutative ring structure which is a domain and a discrete valuation ring, given an $R'$-algebra structure making $R''$ finite, étale and faithfully flat over $R'$, and for every $a \colon \operatorname{Spec} R'' \to Y$ with $a$ followed by $y$ equal to $\operatorname{Spec}$ of $R' \to R''$ followed by $\operatorname{Spec}$ of $R \to R'$, there exists a morphism
--   $$\tau \colon Y \times_R \operatorname{Spec} R'' \longrightarrow Y' \times_{R'} \operatorname{Spec} R''$$
--   (the pullbacks being those of $y$ along the composite $\operatorname{Spec} R'' \to \operatorname{Spec} R$ and of $y'$ along $\operatorname{Spec} R'' \to \operatorname{Spec} R'$) such that $\tau$ followed by the second projection is the second projection, and such that for every scheme $T$ and all morphisms $x \colon T \to Y \times_R \operatorname{Spec} R''$, $w \colon T \to U$ and $v \colon T \to Y \times_R \operatorname{Spec} R'$ satisfying: $w$ followed by $U.\iota$ and $\mathrm{pr}_1$ equals $x$ followed by the second projection and then $a$; $w$ followed by $U.\iota$ and $\mathrm{pr}_2$ equals $x$ followed by the first projection; $v$ followed by the first projection of $Y \times_R \operatorname{Spec} R'$ equals $m \circ w$; and $v$ followed by the second projection equals $x$ followed by the second projection and then $\operatorname{Spec}$ of $R' \to R''$ — one has that $x$ followed by $\tau$ and then the first projection of $Y' \times_{R'} \operatorname{Spec} R''$ equals $v$ followed by $\iota$.
--
--   This is the construction step of Artin's covering argument, following Weil, by which a strict birational group law is shown to come from a group scheme, here in the form valid over a henselian (rather than strictly henselian) discrete valuation ring: after a finite étale extension $R'/R$ one glues translates to $Y$ so as to obtain a scheme $Y'$ with a section on which all left translations by points over finite étale extensions are defined, the original data being carried along by the open immersion $\iota$ and the extended law $m'$. It is used by [`NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing) on the way to the construction of Néron models of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_exists_translation_of_forall_dense_preimage_fibre_of_henselianLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
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
    (hYk : ∃ x : Y, y.base x = IsLocalRing.closedPoint R)
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (Y' : Scheme.{u}) (y' : Y' ⟶ Spec (CommRingCat.of R'))
      (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y')
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
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫ pullback.fst y y ≫ y))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y),
        a.1 = w.1 ≫ U.ι ≫ pullback.fst y y → b.1 = w.1 ≫ U.ι ≫ pullback.snd y y → c.1 = w.1 ≫ m.1 →
        ∃ w' : SchemeHomOver t' (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a).1 ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b).1 ≫ ι.1 ∧
          w'.1 ≫ m'.1 = (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c).1 ≫ ι.1) ∧
      (∃ a' : Spec (CommRingCat.of R') ⟶ Y', a' ≫ y' = 𝟙 _) ∧
      (∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
          (_ : Algebra R' R'') (_ : Module.Finite R' R'') (_ : Algebra.Etale R' R'') (_ : Module.FaithfullyFlat R' R'')
          (a : Spec (CommRingCat.of R'') ⟶ Y),
        a ≫ y = (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R'))) →
        ∃ τ : pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ⟶ pullback y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))),
          τ ≫ pullback.snd y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ∧
          ∀ {T : Scheme.{u}} (x : T ⟶ pullback y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (w : T ⟶ (U : Scheme.{u})) (v : T ⟶ pullback y (Spec.map (CommRingCat.ofHom (algebraMap R R')))),
            w ≫ U.ι ≫ pullback.fst y y = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ a →
            w ≫ U.ι ≫ pullback.snd y y = x ≫ pullback.fst y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) →
            v ≫ pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = w ≫ m.1 →
            v ≫ pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R'))) = x ≫ pullback.snd y ((Spec.map (CommRingCat.ofHom (algebraMap R' R''))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) →
            x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) := by sorry
