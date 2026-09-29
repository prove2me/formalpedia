-- Prove2me | Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- name    : NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/ead86195-242b-5853-a3fb-f3511e15d05a
-- title:
--   Strict birational group laws over henselian discrete valuation rings
-- statement:
--   Let $R$ be a henselian discrete valuation ring with fraction field $K$, let $g_K\colon X_K\to\operatorname{Spec}K$ carry a relative group law $L_{X_K}$ (a functorial group structure on $T$-points over $\operatorname{Spec}K$), and let $f\colon X\to\operatorname{Spec}R$ be smooth, separated, locally of finite type and quasi-compact, with some point above the closed point of $R$, together with $e$, a morphism over $\operatorname{Spec}K$ from the generic fibre $X\times_{\operatorname{Spec}R}\operatorname{Spec}K$ to $X_K$ whose underlying scheme morphism is an isomorphism. Let $W\subseteq X\times_RX$ be open and $m\colon W\to X$ a morphism over $\operatorname{Spec}R$ (via $\mathrm{pr}_1$) such that $W$ contains every point not above the closed point and every point $p$ above the closed point that is maximal there (no $y$ above the closed point with $p$ in the closure of $\{y\}$ other than $p$); on generic fibres $e\circ m$ is the $L_{X_K}$-product of $e\circ\mathrm{pr}_1$ and $e\circ\mathrm{pr}_2$; the translations $\Phi=(\mathrm{pr}_1,m)$ and $\Psi=(m,\mathrm{pr}_2)$ from $W$ to $X\times_RX$ are open immersions whose images contain all such maximal points. Let further $X'\subseteq X$ and $U\subseteq W$ be open, $X'$ containing all points not above the closed point and all maximal points above it, $U$ containing all points not above the closed point, with $\mathrm{pr}_1(q),\mathrm{pr}_2(q),m(q)\in X'$ for $q\in U$, and such that for every $x\in X'$ each of $U$, $\Phi(U)$, $\Psi(U)$ has dense preimage in both fibres $\mathrm{pr}_1^{-1}(x)$ and $\mathrm{pr}_2^{-1}(x)$. Then there are a scheme $g\colon B\to\operatorname{Spec}R$, smooth, separated, locally of finite type and quasi-compact, a relative group law $L_B$ on $g$, a morphism $j\colon X'\to B$ over $\operatorname{Spec}R$ which is an open immersion whose image contains every point of $B$ not above the closed point and every maximal point above it, and an isomorphism $e'$ from the generic fibre of $g$ to $X_K$ over $K$ transporting the group law $L_B$ base-changed to $K$ into $L_{X_K}$ on all $T$-points, such that $e'\circ j$ and $e\circ(X'\hookrightarrow X)$ agree on generic fibres, and such that for every $t\colon T\to\operatorname{Spec}R$, every $T$-point $w$ of $U$ and all $T$-points $a,b,c$ of $X'$ with $a=\mathrm{pr}_1\circ w$, $b=\mathrm{pr}_2\circ w$ and $c=m\circ w$ in $X$, one has $j\circ c=L_B(j\circ a,j\circ b)$.
--
--   This is the henselian case of the theorem that a strict birational group law over a discrete valuation ring has a solution, as in Bosch–Lütkebohmert–Raynaud, Néron Models 6.5, Corollary 2, with the group structure on the generic fibre prescribed. It is obtained by combining the construction of a finite étale solution with the descent of such a solution to $R$, and feeds the construction of smooth group models with prescribed generic fibre used in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing
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
