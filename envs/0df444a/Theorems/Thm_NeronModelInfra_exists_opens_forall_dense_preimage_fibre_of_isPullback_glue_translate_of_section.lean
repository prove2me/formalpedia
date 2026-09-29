-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
-- name    : NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/beed39eb-7fd4-533c-8cf4-bf0de66d0a03
-- title:
--   Strict birational group law extends along a translate gluing
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $y \colon Y \to \operatorname{Spec}(R)$ be a morphism of schemes which is smooth, separated, locally of finite type and quasi-compact. Write $\mathrm{pr}_1 =$ `pullback.fst y y` and $\mathrm{pr}_2 =$ `pullback.snd y y` for the two projections of $Y \times_R Y$. Let $U$ be an open subscheme of $Y \times_R Y$, with open immersion $U.\iota$, and let $m$ be an element of `SchemeHomOver (U.ι ≫ pullback.fst y y ≫ y) y`, that is, a morphism $m \colon U \to Y$ together with the identity $m \mathbin{;} y = U.\iota \mathbin{;} \mathrm{pr}_1 \mathbin{;} y$ (a morphism over $\operatorname{Spec}(R)$). Throughout, for a point $x$ of $Y$ and for a subset $S$ of the underlying space of $Y \times_R Y$, the density conditions refer to the preimage of $S$ under the inclusion of the set-theoretic fibre $\{q : \mathrm{pr}_i(q) = x\}$, with its subspace topology, into that space.
--
--   The hypotheses on $(U,m)$ are these. **Fibrewise density of $U$:** `hU₁` and `hU₂` state that for every point $x$ of $Y$ the preimage of $U$ in the $\mathrm{pr}_1$-fibre over $x$, respectively in the $\mathrm{pr}_2$-fibre over $x$, is dense. **Universal translations:** $\Phi$ denotes the morphism $U \to Y \times_R Y$ obtained from the pair $(U.\iota \mathbin{;} \mathrm{pr}_1, m)$ and $\Psi$ the morphism obtained from the pair $(m, U.\iota \mathbin{;} \mathrm{pr}_2)$; `hΦ` and `hΨ` assert that $\Phi$ and $\Psi$ are open immersions, and `hΦ₁`, `hΦ₂`, `hΨ₁`, `hΨ₂` assert that for every point $x$ of $Y$ the preimage of the set-theoretic range of $\Phi$, respectively of $\Psi$, is dense in the $\mathrm{pr}_1$-fibre and in the $\mathrm{pr}_2$-fibre over $x$. **Associativity on points:** `hassoc` states that for every scheme $T$, every $t \colon T \to \operatorname{Spec}(R)$ and all $u, v, p, q$ in `SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)` (morphisms $T \to U$ compatible with $t$), if $u \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_2 = v \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_1$, $p \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_1 = u \mathbin{;} m$, $p \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_2 = v \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_2$, $q \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_1 = u \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_1$ and $q \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_2 = v \mathbin{;} m$, then $p \mathbin{;} m = q \mathbin{;} m$; in the notation $u = (b,c)$, $v = (c,d)$, $p = (bc,d)$, $q = (b,cd)$ this is $(bc)d = b(cd)$.
--
--   The remaining data concern the closure of the graph and the gluing. Let $\gamma \colon G \to (Y \times_R Y) \times_R Y$ (formed as `pullback (pullback.fst y y ≫ y) y`) be a closed immersion whose set-theoretic range equals, by `hΓ`, the closure of the range of the morphism $U \to (Y \times_R Y) \times_R Y$ given by the pair $(U.\iota, m)$, i.e. of the graph of $m$. Three further hypotheses require that $\gamma$ followed by the projection to $Y \times_R Y$, $\gamma$ followed by the morphism to $Y \times_R Y$ taking the first and third coordinates, and $\gamma$ followed by the morphism to $Y \times_R Y$ taking the second and third coordinates, are all open immersions. Let $a \colon \operatorname{Spec}(R) \to Y$ be a section, $a \mathbin{;} y = \mathrm{id}$.
--
--   Let $y' \colon Y' \to \operatorname{Spec}(R)$ be smooth, separated, locally of finite type and quasi-compact, and let $\iota, \tau$ be two morphisms $Y \to Y'$ over $\operatorname{Spec}(R)$ (elements of `SchemeHomOver y y'`) whose underlying morphisms are open immersions. **Covering:** `hcov` states that every point of $Y'$ lies in the range of $\iota$ or in the range of $\tau$. **Gluing square:** let $P$ be the fibre product of $\gamma$ with the morphism $Y \times_R Y \to (Y \times_R Y) \times_R Y$ sending a point with coordinates $(b,c)$ to $((a, b), c)$ — formed from the pair consisting of the morphism $(\mathrm{pr}_1 \mathbin{;} y \mathbin{;} a, \mathrm{pr}_1)$ into $Y \times_R Y$ and of $\mathrm{pr}_2$ — and let $\delta$ be the projection $P \to Y \times_R Y$. Then `hΓa` asserts that the square with the two morphisms $\delta \mathbin{;} \mathrm{pr}_1$ and $\delta \mathbin{;} \mathrm{pr}_2$ from $P$ to $Y$ and the two morphisms $\tau$, $\iota$ from $Y$ to $Y'$ is a pullback square (`IsPullback`), so that $Y'$ is obtained by gluing two copies of $Y$ along the slice of $G$ above the section $a$, with $\tau$ as the translated chart.
--
--   Under these hypotheses there exist an open subscheme $U'$ of $Y' \times_R Y'$ and an element $m'$ of `SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'`, i.e. a morphism $m' \colon U' \to Y'$ with $m' \mathbin{;} y' = U'.\iota \mathbin{;} \mathrm{pr}'_1 \mathbin{;} y'$, such that, writing $\mathrm{pr}'_1, \mathrm{pr}'_2$ for the projections of $Y' \times_R Y'$ and $\Phi' = (U'.\iota \mathbin{;} \mathrm{pr}'_1, m')$, $\Psi' = (m', U'.\iota \mathbin{;} \mathrm{pr}'_2)$ for the corresponding morphisms $U' \to Y' \times_R Y'$, the following nine statements hold:
--
--   (1) for every point $x$ of $Y'$ the preimage of $U'$ in the $\mathrm{pr}'_1$-fibre over $x$ is dense;
--   (2) for every point $x$ of $Y'$ the preimage of $U'$ in the $\mathrm{pr}'_2$-fibre over $x$ is dense;
--   (3) $\Phi'$ is an open immersion;
--   (4) for every point $x$ of $Y'$ the preimage of the range of $\Phi'$ in the $\mathrm{pr}'_1$-fibre over $x$ is dense;
--   (5) the same for the $\mathrm{pr}'_2$-fibres;
--   (6) $\Psi'$ is an open immersion;
--   (7) for every point $x$ of $Y'$ the preimage of the range of $\Psi'$ in the $\mathrm{pr}'_1$-fibre over $x$ is dense;
--   (8) the same for the $\mathrm{pr}'_2$-fibres;
--   (9) $m'$ is associative on points in the sense of `hassoc` above, with $(U', m', y')$ in place of $(U, m, y)$: for every scheme $T$, every $t \colon T \to \operatorname{Spec}(R)$ and all $u, v, p, q$ in `SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')`, the five relations $u \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_2 = v \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_1$, $p \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_1 = u \mathbin{;} m'$, $p \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_2 = v \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_2$, $q \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_1 = u \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_1$, $q \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_2 = v \mathbin{;} m'$ imply $p \mathbin{;} m' = q \mathbin{;} m'$;
--
--   and finally (10) $m'$ extends $m$ along $\iota$ on points: for every scheme $T$, every $t \colon T \to \operatorname{Spec}(R)$ and every $w$ in `SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)` there exists $w'$ in `SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')` with $w' \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_1 = w \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_1 \mathbin{;} \iota$, $w' \mathbin{;} U'.\iota \mathbin{;} \mathrm{pr}'_2 = w \mathbin{;} U.\iota \mathbin{;} \mathrm{pr}_2 \mathbin{;} \iota$ and $w' \mathbin{;} m' = w \mathbin{;} m \mathbin{;} \iota$.
--
--   This is the scheme-theoretic step, for a discrete valuation ring as base, by which an associative strict birational group law on a smooth separated $R$-scheme $Y$ of finite type is transported to the scheme obtained by gluing $Y$ to a translate of itself by a section, as in Bosch–Lütkebohmert–Raynaud, Néron Models, 5.3. It feeds the construction of group laws in the smoothening/Néron model machinery and is used by [`NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre`](thm.html#NeronModelInfra.exists_glue_translate_baseChange_isOpenImmersion_forall_range_subset_of_forall_dense_preimage_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_forall_dense_preimage_fibre_of_isPullback_glue_translate_of_section
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
    {G : Scheme.{u}} (γ : G ⟶ pullback (pullback.fst y y ≫ y) y) [IsClosedImmersion γ]
    (hΓ : Set.range γ.base =
      closure (Set.range (pullback.lift (f := pullback.fst y y ≫ y) (g := y) U.ι m.1 m.2.symm).base))
    [IsOpenImmersion (γ ≫ pullback.fst (pullback.fst y y ≫ y) y)]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.fst y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc]; exact pullback.condition))]
    [IsOpenImmersion (γ ≫ pullback.lift (f := y) (g := y)
        (pullback.fst (pullback.fst y y ≫ y) y ≫ pullback.snd y y) (pullback.snd (pullback.fst y y ≫ y) y)
        (by rw [Category.assoc, ← pullback.condition (f := y) (g := y)]; exact pullback.condition))]
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι τ : SchemeHomOver y y') [IsOpenImmersion ι.1] [IsOpenImmersion τ.1]
    (hcov : ∀ p : Y', p ∈ Set.range ι.1.base ∨ p ∈ Set.range τ.1.base)
    (hΓa : IsPullback
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.fst y y)
        (pullback.snd γ
            (pullback.lift (f := pullback.fst y y ≫ y) (g := y)
              (pullback.lift (f := y) (g := y) (pullback.fst y y ≫ y ≫ a) (pullback.fst y y)
                (by rw [Category.assoc, Category.assoc, ha, Category.comp_id]))
              (pullback.snd y y)
              (by rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, ha, Category.comp_id,
                pullback.condition])) ≫ pullback.snd y y)
        τ.1 ι.1) :
    ∃ (U' : (pullback y' y').Opens) (m' : SchemeHomOver (U'.ι ≫ pullback.fst y' y' ≫ y') y'),
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
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.fst y' y' →
        p.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ m'.1 →
        p.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ U'.ι ≫ pullback.snd y' y' →
        q.1 ≫ U'.ι ≫ pullback.fst y' y' = u.1 ≫ U'.ι ≫ pullback.fst y' y' →
        q.1 ≫ U'.ι ≫ pullback.snd y' y' = v.1 ≫ m'.1 →
        p.1 ≫ m'.1 = q.1 ≫ m'.1) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y)),
        ∃ w' : SchemeHomOver t (U'.ι ≫ pullback.fst y' y' ≫ y'),
          w'.1 ≫ U'.ι ≫ pullback.fst y' y' = w.1 ≫ U.ι ≫ pullback.fst y y ≫ ι.1 ∧
          w'.1 ≫ U'.ι ≫ pullback.snd y' y' = w.1 ≫ U.ι ≫ pullback.snd y y ≫ ι.1 ∧
          w'.1 ≫ m'.1 = w.1 ≫ m.1 ≫ ι.1) := by sorry
