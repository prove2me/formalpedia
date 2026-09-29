-- Prove2me | Theorems.Thm_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
-- name    : NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/3e7fa3c9-64b3-526f-8954-3b387efdbd8a
-- title:
--   Enlarging the domain of m' over a henselian base
-- statement:
--   Throughout, $R$ is a commutative ring which is a domain and a discrete valuation ring, and is moreover a henselian local ring; $y \colon Y \to \operatorname{Spec} R$ is a morphism of schemes which is smooth, separated, locally of finite type and quasi-compact. For such a $y$ the fibre product $Y \times_R Y$ is written `pullback y y`, with projections $\mathrm{pr}_1 =$ `pullback.fst y y` and $\mathrm{pr}_2 =$ `pullback.snd y y`. An open subscheme $U$ of $Y \times_R Y$ is given, with inclusion `U.ι`, together with $m$, which is a morphism $U \to Y$ together with a proof that $m$ followed by $y$ equals `U.ι` followed by $\mathrm{pr}_1$ followed by $y$; thus $m$ is a morphism over $\operatorname{Spec} R$. Write $\Phi$ for the morphism $U \to Y \times_R Y$ with components (`U.ι` followed by $\mathrm{pr}_1$) and $m$, and $\Psi$ for the morphism $U \to Y \times_R Y$ with components $m$ and (`U.ι` followed by $\mathrm{pr}_2$).
--
--   The hypotheses on the unprimed data fall into four groups. (i) Density of $U$ in the fibres: `hU₁` and `hU₂` say that for every point $x$ of $Y$ the preimage of $U$ under the inclusion of the subspace $\{q \in Y \times_R Y : \mathrm{pr}_1(q) = x\}$, respectively of $\{q : \mathrm{pr}_2(q) = x\}$, is dense in that subspace. (ii) Openness and fibrewise density for the two universal translations: `hΦ` asserts that $\Phi$ is an open immersion, and `hΦ₁`, `hΦ₂` that for every $x$ in $Y$ the preimage of the set-theoretic image of $\Phi$ is dense in the $\mathrm{pr}_1$-fibre, respectively the $\mathrm{pr}_2$-fibre, over $x$; `hΨ`, `hΨ₁`, `hΨ₂` are the same three assertions for $\Psi$. (iii) Associativity `hassoc`: for every scheme $T$, every $t \colon T \to \operatorname{Spec} R$ and all four $T$-points $u, v, p, q$ of $U$ over $t$ (each being a morphism $T \to U$ whose composition with `U.ι`, $\mathrm{pr}_1$ and $y$ is $t$), if $\mathrm{pr}_2 \circ u = \mathrm{pr}_1 \circ v$, $\mathrm{pr}_1 \circ p = m \circ u$, $\mathrm{pr}_2 \circ p = \mathrm{pr}_2 \circ v$, $\mathrm{pr}_1 \circ q = \mathrm{pr}_1 \circ u$ and $\mathrm{pr}_2 \circ q = m \circ v$ (all projections read after `U.ι`), then $m \circ p = m \circ q$. (iv) `hUK`: every point $q$ of $Y \times_R Y$ whose image under $\mathrm{pr}_1$ followed by $y$ is not the closed point of $\operatorname{Spec} R$ belongs to $U$; that is, $U$ contains the whole generic fibre of $Y \times_R Y$.
--
--   Next, $R'$ is a commutative ring which is a domain and a discrete valuation ring, an $R$-algebra that is module-finite, étale and faithfully flat over $R$; $y' \colon Y' \to \operatorname{Spec} R'$ is smooth, separated, locally of finite type and quasi-compact; and $\iota$ is a morphism $Y \times_R \operatorname{Spec} R' \to Y'$ over $\operatorname{Spec} R'$ (a morphism together with a proof that it followed by $y'$ is the projection `pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))`) whose underlying morphism is an open immersion. An open subscheme $U'$ of $Y' \times_{R'} Y'$ and a morphism $m' \colon U' \to Y'$ over $\operatorname{Spec} R'$ (in the same sense as $m$, with $y'$ in place of $y$) are given, subject to the primed analogues `hU'₁`, `hU'₂`, `hΦ'`, `hΦ'₁`, `hΦ'₂`, `hΨ'`, `hΨ'₁`, `hΨ'₂`, `hassoc'` of the groups (i)–(iii) above, formulated for $Y'$, $U'$, $m'$ over $\operatorname{Spec} R'$; no analogue of `hUK` is assumed for $U'$.
--
--   Two further hypotheses link the two levels. The compatibility hypothesis `hext` states: for every scheme $T$, every $t' \colon T \to \operatorname{Spec} R'$, every $T$-point $w$ of $U$ over $t'$ followed by $\operatorname{Spec}$ of $R \to R'$, and all $T$-points $a, b, c$ of $Y$ over that same composite with $a = w$ followed by `U.ι` and $\mathrm{pr}_1$, $b = w$ followed by `U.ι` and $\mathrm{pr}_2$, and $c = m \circ w$, there is a $T$-point $w'$ of $U'$ over $t'$ such that $w'$ followed by `U'.ι` and $\mathrm{pr}_1$ equals $\iota$ precomposed with the base-changed point `RelativeGroupLaw.baseChangePointOfBase` of $a$ (the point of $Y \times_R \operatorname{Spec} R'$ with components $a$ and $t'$), $w'$ followed by `U'.ι` and $\mathrm{pr}_2$ is the corresponding expression for $b$, and $m' \circ w'$ is the corresponding expression for $c$. Thus $m'$ extends $m$ along $\iota$ on $T$-points. The hypothesis `hstat` on extendability of left translations states: for every $R''$ which is a commutative ring, a domain, a discrete valuation ring and an $R'$-algebra that is module-finite, étale and faithfully flat over $R'$, and every morphism $a \colon \operatorname{Spec} R'' \to Y$ with $a$ followed by $y$ equal to $\operatorname{Spec}$ of $R' \to R''$ followed by $\operatorname{Spec}$ of $R \to R'$, there exists a morphism $\tau \colon Y \times_R \operatorname{Spec} R'' \to Y' \times_{R'} \operatorname{Spec} R''$ such that $\tau$ followed by the projection to $\operatorname{Spec} R''$ is the projection to $\operatorname{Spec} R''$, and such that for every scheme $T$ and all morphisms $x \colon T \to Y \times_R \operatorname{Spec} R''$, $w \colon T \to U$ and $v \colon T \to Y \times_R \operatorname{Spec} R'$ satisfying: $w$ followed by `U.ι` and $\mathrm{pr}_1$ equals $x$ followed by the projection to $\operatorname{Spec} R''$ followed by $a$; $w$ followed by `U.ι` and $\mathrm{pr}_2$ equals the $Y$-component of $x$; the $Y$-component of $v$ equals $m \circ w$; and the $\operatorname{Spec} R'$-component of $v$ equals the $\operatorname{Spec} R''$-component of $x$ followed by $\operatorname{Spec}$ of $R' \to R''$ — one has $x$ followed by $\tau$ followed by the projection to $Y'$ equal to $v$ followed by $\iota$. In other words the left translation by $a$, followed by $\iota$, extends to all of $Y \times_R \operatorname{Spec} R''$.
--
--   Under these hypotheses the conclusion asserts the existence of an open subscheme $U''$ of $Y' \times_{R'} Y'$, an inequality $U' \le U''$, and a morphism $m'' \colon U'' \to Y'$ over $\operatorname{Spec} R'$ (a morphism together with a proof that it followed by $y'$ equals `U''.ι` followed by $\mathrm{pr}_1$ and $y'$) such that, writing $\Phi''$ for the morphism $U'' \to Y' \times_{R'} Y'$ with components (`U''.ι` followed by $\mathrm{pr}_1$) and $m''$, and $\Psi''$ for the one with components $m''$ and (`U''.ι` followed by $\mathrm{pr}_2$), the following ten statements hold: the open immersion $U' \to U''$ given by `homOfLE` followed by $m''$ equals $m'$; for every $x$ in $Y'$ the preimage of $U''$ in the $\mathrm{pr}_1$-fibre over $x$ is dense; likewise in the $\mathrm{pr}_2$-fibre over $x$; $\Phi''$ is an open immersion; for every $x$ the preimage of the image of $\Phi''$ is dense in the $\mathrm{pr}_1$-fibre over $x$; and dense in the $\mathrm{pr}_2$-fibre over $x$; $\Psi''$ is an open immersion; for every $x$ the preimage of the image of $\Psi''$ is dense in the $\mathrm{pr}_1$-fibre over $x$; and dense in the $\mathrm{pr}_2$-fibre over $x$; the associativity condition of group (iii) holds for $U''$ and $m''$, namely for every scheme $T$, every $t \colon T \to \operatorname{Spec} R'$ and all $T$-points $u, v, p, q$ of $U''$ over $t$, the five equations $\mathrm{pr}_2 \circ u = \mathrm{pr}_1 \circ v$, $\mathrm{pr}_1 \circ p = m'' \circ u$, $\mathrm{pr}_2 \circ p = \mathrm{pr}_2 \circ v$, $\mathrm{pr}_1 \circ q = \mathrm{pr}_1 \circ u$, $\mathrm{pr}_2 \circ q = m'' \circ v$ (projections read after `U''.ι`) imply $m'' \circ p = m'' \circ q$; and finally every point $q$ of $Y' \times_{R'} Y'$ such that both $\mathrm{pr}_1(q)$ and $\mathrm{pr}_2(q)$ lie in the set-theoretic image of $\iota$ belongs to $U''$.
--
--   This is the definedness half of the construction of a group scheme from a strict birational group law, in the shape of Bosch–Lütkebohmert–Raynaud, Néron Models 5.3, Lemma 6, adapted to a henselian discrete valuation base: the extendability of all left translations by points valued in finite étale discrete valuation extensions forces the domain of $m'$ to be enlargeable so as to contain all pairs of points coming from $Y \times_R \operatorname{Spec} R'$. It feeds into [`NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing), part of the Néron model input to the good-reduction analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_opens_forall_mem_of_mem_range_of_forall_exists_translation_of_henselianLocalRing
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
    (hUK : ∀ q : ↑(pullback y y), (pullback.fst y y ≫ y).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {Y' : Scheme.{u}} (y' : Y' ⟶ Spec (CommRingCat.of R'))
    [Smooth y'] [IsSeparated y'] [LocallyOfFiniteType y'] [QuasiCompact y']
    (ι : SchemeHomOver (pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap R R')))) y') [IsOpenImmersion ι.1]
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
    (hstat : ∀ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
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
          x ≫ τ ≫ pullback.fst y' (Spec.map (CommRingCat.ofHom (algebraMap R' R''))) = v ≫ ι.1) :
    ∃ (U'' : (pullback y' y').Opens) (hle : U' ≤ U'')
      (m'' : SchemeHomOver (U''.ι ≫ pullback.fst y' y' ≫ y') y'),
      (pullback y' y').homOfLE hle ≫ m''.1 = m'.1 ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U'' : Set ↑(pullback y' y')))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (U'' : Set ↑(pullback y' y')))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') (U''.ι ≫ pullback.fst y' y') m''.1
            ((Category.assoc _ _ _).trans m''.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.fst y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback y' y') // (pullback.snd y' y').base q = x} → ↑(pullback y' y')) ⁻¹'
          (Set.range (pullback.lift (f := y') (g := y') m''.1 (U''.ι ≫ pullback.snd y' y')
            (m''.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
          (u v p q : SchemeHomOver t (U''.ι ≫ pullback.fst y' y' ≫ y')),
        u.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ U''.ι ≫ pullback.fst y' y' →
        p.1 ≫ U''.ι ≫ pullback.fst y' y' = u.1 ≫ m''.1 →
        p.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ U''.ι ≫ pullback.snd y' y' →
        q.1 ≫ U''.ι ≫ pullback.fst y' y' = u.1 ≫ U''.ι ≫ pullback.fst y' y' →
        q.1 ≫ U''.ι ≫ pullback.snd y' y' = v.1 ≫ m''.1 →
        p.1 ≫ m''.1 = q.1 ≫ m''.1) ∧
      (∀ q : ↑(pullback y' y'), (pullback.fst y' y').base q ∈ Set.range ι.1.base →
        (pullback.snd y' y').base q ∈ Set.range ι.1.base → q ∈ U'') := by sorry
