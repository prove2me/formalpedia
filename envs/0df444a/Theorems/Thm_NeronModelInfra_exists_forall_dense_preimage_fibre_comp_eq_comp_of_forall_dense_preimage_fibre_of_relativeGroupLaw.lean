-- Prove2me | Theorems.Thm_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
-- name    : NeronModelInfra.exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/e4f873ea-6bde-54e1-bfed-ccfc5e5b4c28
-- title:
--   Restricting a birational group law to an open subscheme
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain which is a discrete valuation ring) and let $K$ be a field which is a fraction field of $R$ via the given $R$-algebra structure; write $\operatorname{Spec} K \to \operatorname{Spec} R$ for the morphism `specGenericFibreInclusion R K` induced by $R \to K$.
--
--   The data are as follows. A scheme $X_K$ with a structure morphism $g_K \colon X_K \to \operatorname{Spec} K$ together with a term `LXK : RelativeGroupLaw K gK`, that is, functorial operations assigning to each $K$-scheme $t \colon T \to \operatorname{Spec} K$ a multiplication, a unit and an inversion on the set of $T$-points of $X_K$ over $\operatorname{Spec} K$, subject to associativity, the two unit laws, left inversion, and naturality of the multiplication under base change along morphisms $T' \to T$ over $\operatorname{Spec} K$. Further, a morphism $f \colon X \to \operatorname{Spec} R$ which is smooth, separated, locally of finite type and quasi-compact; a morphism $e.1$ from the generic fibre $X \times_{\operatorname{Spec} R} \operatorname{Spec} K$ (taken with its second projection as structure morphism over $\operatorname{Spec} K$) to $X_K$ satisfying $e.1 \circ$ followed by $g_K$ equal to that second projection, and $e.1$ is an isomorphism.
--
--   Next, an open subscheme $W$ of $X \times_{\operatorname{Spec} R} X$ and a term $m$ of `SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f`, i.e. a morphism $m.1 \colon W \to X$ with $m.1$ followed by $f$ equal to the inclusion $W \hookrightarrow X \times_R X$ followed by the first projection and by $f$.
--
--   The hypotheses are grouped as follows.
--
--   (i) Compatibility with the group law on the generic fibre, `hmK`: the base change of $m$ to $K$ (`genericFibreRestrict`), followed by $e$, coincides with the morphism obtained by restricting along the map of pullbacks $W \times_R \operatorname{Spec} K \to (X \times_R X) \times_R \operatorname{Spec} K$ induced by $W.ι$ and the identity on $\operatorname{Spec} K$ and $\operatorname{Spec} R$, the product formed by `LXK.mul`, at the $K$-scheme $(X \times_R X) \times_R \operatorname{Spec} K$, of the base changes to $K$ of the two projections $\mathrm{pr}_1, \mathrm{pr}_2 \colon X \times_R X \to X$, each followed by $e$. In other words, on the generic fibre $e(m(x,y)) = e(x) \cdot e(y)$.
--
--   (ii) The two universal translations are open immersions: `hΦ` states that $\Phi = (W.ι \text{ followed by } \mathrm{pr}_1,\; m.1) \colon W \to X \times_R X$ is an open immersion, and `hΨ` states that $\Psi = (m.1,\; W.ι \text{ followed by } \mathrm{pr}_2) \colon W \to X \times_R X$ is an open immersion.
--
--   (iii) An open subscheme $X'$ of $X$ and an open subscheme $U$ of $X \times_R X$ with $U \le W$ (`hUW`), subject to: `hU₁`, every point $q$ of $X \times_R X$ whose image under $\mathrm{pr}_1$ followed by $f$ is not the closed point of $R$ lies in $U$ (so $U$ contains the generic fibre); `hU₂`, for every $q \in U$ the three points $\mathrm{pr}_1(q)$, $\mathrm{pr}_2(q)$ and $m.1(q)$ (the last taken at $q$ regarded as a point of $W$) lie in $X'$; and `hU₃`, for every point $x$ of $X$ lying in $X'$, six density clauses, each asserting that the preimage of a set along the inclusion of a fibre $\{q : \mathrm{pr}_i(q) = x\}$ (with its subspace topology) into the space of $X \times_R X$ is dense: for $i = 1, 2$ the preimage of $U$, the preimage of the image under $\Phi$ of $\{w \in W : W.ι(w) \in U\}$, and the preimage of the image under $\Psi$ of the same set.
--
--   The conclusion asserts the existence of an open subscheme $U_Y$ of $X' \times_{\operatorname{Spec} R} X'$ — the pullback of $X'.ι$ followed by $f$ with itself — and of a term $m_Y$ of `SchemeHomOver (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f)`, i.e. a morphism $m_Y.1 \colon U_Y \to X'$ over $\operatorname{Spec} R$ whose composite with $X'.ι$ followed by $f$ is the inclusion $U_Y \hookrightarrow X' \times_R X'$ followed by the first projection and the structure morphism, such that the following nine statements hold, where $\Phi_Y = (U_Y.ι \text{ followed by } \mathrm{pr}_1,\; m_Y.1)$ and $\Psi_Y = (m_Y.1,\; U_Y.ι \text{ followed by } \mathrm{pr}_2)$ are morphisms $U_Y \to X' \times_R X'$ and the fibres are those of the two projections of $X' \times_R X'$:
--
--   1. For every point $x$ of $X'$, the preimage of $U_Y$ in the fibre $\{q : \mathrm{pr}_1(q) = x\}$ is dense.
--
--   2. For every point $x$ of $X'$, the preimage of $U_Y$ in the fibre $\{q : \mathrm{pr}_2(q) = x\}$ is dense.
--
--   3. $\Phi_Y$ is an open immersion.
--
--   4. For every $x$, the preimage of the range of $\Phi_Y$ on points in the fibre $\{q : \mathrm{pr}_1(q) = x\}$ is dense.
--
--   5. The same with the fibre of $\mathrm{pr}_2$.
--
--   6. $\Psi_Y$ is an open immersion.
--
--   7. For every $x$, the preimage of the range of $\Psi_Y$ on points in the fibre $\{q : \mathrm{pr}_1(q) = x\}$ is dense.
--
--   8. The same with the fibre of $\mathrm{pr}_2$.
--
--   9. Associativity in the form: for every scheme $T$ with a morphism $t \colon T \to \operatorname{Spec} R$ and every four $T$-points $u, v, p, q$ of $U_Y$ over $\operatorname{Spec} R$ (elements of `SchemeHomOver t (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f))`), if the second component of $u$ equals the first component of $v$, if the first component of $p$ equals $u$ followed by $m_Y.1$ and the second component of $p$ equals the second component of $v$, and if the first component of $q$ equals the first component of $u$ and the second component of $q$ equals $v$ followed by $m_Y.1$, then $p$ followed by $m_Y.1$ equals $q$ followed by $m_Y.1$; that is, with $u = (a,b)$, $v = (b,c)$, $p = (ab, c)$, $q = (a, bc)$, one has $(ab)c = a(bc)$.
--
--   10. Every point $q$ of $X' \times_R X'$ whose image under the first projection followed by $X'.ι$ and $f$ is not the closed point of $R$ lies in $U_Y$.
--
--   11. Compatibility of $(U_Y, m_Y)$ with $(U, m)$: for every scheme $T$, every morphism $w \colon T \to U$ and every pair of morphisms $a, b \colon T \to X'$ with $a$ followed by $X'.ι$ equal to $w$ followed by $U.ι$ and $\mathrm{pr}_1$, and $b$ followed by $X'.ι$ equal to $w$ followed by $U.ι$ and $\mathrm{pr}_2$, there is a morphism $v \colon T \to U_Y$ whose two components are $a$ and $b$, and such that $v$ followed by $m_Y.1$ and $X'.ι$ equals $w$ followed by the inclusion $U \to W$ given by `hUW` and then by $m.1$.
--
--   (The total number of conjuncts in the conclusion is as listed: two density clauses for $U_Y$, then for each of $\Phi_Y$ and $\Psi_Y$ an open-immersion clause and two density clauses, then the associativity clause, the clause that $U_Y$ contains the generic fibre, and the compatibility clause.)
--
--   This is the passage from a birational group law on $X$ with group generic fibre to a strict birational group law on an open subscheme $X'$, as in the reduction of the Néron-model construction of Bosch–Lütkebohmert–Raynaud (Néron Models, 5.1 Theorem 5 via 5.2 Lemma 2): the new law is $m$ restricted to $U$ with values in $X'$, and the density and open-immersion conditions are transported along the open immersion $X' \times_R X' \hookrightarrow X \times_R X$, associativity being obtained from the generic-fibre group law. It is used in the next step of the construction, [`NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing`](thm.html#NeronModelInfra.exists_finite_etale_isOpenImmersion_forall_mem_of_mem_range_of_forall_dense_preimage_fibre_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_forall_dense_preimage_fibre_comp_eq_comp_of_forall_dense_preimage_fibre_of_relativeGroupLaw
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
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
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
    ∃ (UY : (pullback (X'.ι ≫ f) (X'.ι ≫ f)).Opens)
      (mY : SchemeHomOver (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)) (X'.ι ≫ f)),
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (UY : Set ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)) mY.1
            ((Category.assoc _ _ _).trans mY.2.symm)).base))) ∧
      IsOpenImmersion
          (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ x, Dense ((Subtype.val : {q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)) // (pullback.snd (X'.ι ≫ f) (X'.ι ≫ f)).base q = x} → ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f))) ⁻¹'
          (Set.range (pullback.lift (f := (X'.ι ≫ f)) (g := (X'.ι ≫ f)) mY.1 (UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f))
            (mY.2.trans (by rw [Category.assoc, pullback.condition]))).base))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (u v p q : SchemeHomOver t (UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f))),
        u.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) →
        p.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ mY.1 →
        p.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = u.1 ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) →
        q.1 ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = v.1 ≫ mY.1 →
        p.1 ≫ mY.1 = q.1 ≫ mY.1) ∧
      (∀ q : ↑(pullback (X'.ι ≫ f) (X'.ι ≫ f)),
        (pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) ≫ (X'.ι ≫ f)).base q ≠ IsLocalRing.closedPoint R → q ∈ UY) ∧
      (∀ {T : Scheme.{u}} (w : T ⟶ (U : Scheme.{u})) (a b : T ⟶ (X' : Scheme.{u})),
        a ≫ X'.ι = w ≫ U.ι ≫ pullback.fst f f → b ≫ X'.ι = w ≫ U.ι ≫ pullback.snd f f →
        ∃ v : T ⟶ (UY : Scheme.{u}),
          v ≫ UY.ι ≫ pullback.fst (X'.ι ≫ f) (X'.ι ≫ f) = a ∧ v ≫ UY.ι ≫ pullback.snd (X'.ι ≫ f) (X'.ι ≫ f) = b ∧
          v ≫ mY.1 ≫ X'.ι = w ≫ (pullback f f).homOfLE hUW ≫ m.1) := by sorry
