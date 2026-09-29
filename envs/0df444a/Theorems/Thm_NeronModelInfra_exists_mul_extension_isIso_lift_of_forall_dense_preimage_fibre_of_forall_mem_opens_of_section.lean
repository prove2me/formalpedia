-- Prove2me | Theorems.Thm_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
-- name    : NeronModelInfra.exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/6a8114f1-f70f-59ae-bd22-2f25194008cf
-- title:
--   Birational group law with a section extends to the product
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain) and let $y\colon Y\to\operatorname{Spec} R$ be a smooth, separated, quasi-compact morphism locally of finite type. Let $U$ be an open subscheme of $Y\times_R Y$ and let $m$ be a morphism $U\to Y$ over $\operatorname{Spec} R$, i.e. a pair consisting of $m_1\colon U\to Y$ together with the identity $m_1\circ y=y\circ\mathrm{pr}_1\circ\iota_U$. Assume: for every point $x$ of $Y$, the preimage of $U$ inside the subspace of points $q$ of $Y\times_R Y$ with $\mathrm{pr}_1(q)=x$ is dense, and likewise for $\mathrm{pr}_2$; the universal translations $\Phi=(\mathrm{pr}_1\circ\iota_U,m_1)$ and $\Psi=(m_1,\mathrm{pr}_2\circ\iota_U)$, viewed as morphisms $U\to Y\times_R Y$, are open immersions whose set-theoretic images meet every such $\mathrm{pr}_1$-fibre and every $\mathrm{pr}_2$-fibre densely; and associativity holds in the following functorial form: for every scheme $T$ with a structure morphism $t\colon T\to\operatorname{Spec} R$ and all $T$-valued points $u,v,p,q$ of $U$ over $t$, if the second component of $u$ agrees with the first of $v$, the first of $p$ is $u$ followed by $m_1$ and the second of $p$ is the second of $v$, while the first of $q$ is the first of $u$ and the second of $q$ is $v$ followed by $m_1$, then $p$ followed by $m_1$ equals $q$ followed by $m_1$. Assume further that $y$ admits a section $a$ with $a\circ y=\mathrm{id}$, and that there is an open subscheme $Y_0\subseteq Y$ containing every point $p$ of $Y$ with the property that any $p'$ specialising to $p$ and lying in the same fibre of $y$ equals $p$, and such that every $q\in Y\times_R Y$ with $\mathrm{pr}_1(q)\in Y_0$ and $\mathrm{pr}_2(q)\in Y_0$ lies in $U$. Then there exists a morphism $M\colon Y\times_R Y\to Y$ with $M\circ y=y\circ\mathrm{pr}_1$ such that $\iota_U$ followed by $M$ equals $m_1$, and such that both $(\mathrm{pr}_1,M)$ and $(M,\mathrm{pr}_2)$ are isomorphisms of $Y\times_R Y$.
--
--   This is the extension step in the theory of birational group laws: a strict birational group law on a smooth separated $R$-scheme of finite type admitting a section, which is defined on the square of a suitable open subscheme, is in fact defined on the whole of $Y\times_R Y$, and the resulting left and right translations are global isomorphisms (equivalently, left and right division are everywhere-defined morphisms). It corresponds to the first half of the proof of Lemma 8 in §5.3 of Bosch–Lütkebohmert–Raynaud, and is used to produce the relative group law in [`NeronModelInfra.exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section`](thm.html#NeronModelInfra.exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section), a step in the construction of Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_mul_extension_isIso_lift_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
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
    (a : Spec (CommRingCat.of R) ⟶ Y) (ha : a ≫ y = 𝟙 _)
    (Y₀ : Y.Opens)
    (hY₀ : ∀ p : Y, (∀ p' : Y, p' ⤳ p → y.base p' = y.base p → p' = p) → p ∈ Y₀)
    (hY₀U : ∀ q : ↑(pullback y y), (pullback.fst y y).base q ∈ Y₀ → (pullback.snd y y).base q ∈ Y₀ → q ∈ U) :
    ∃ M : SchemeHomOver (pullback.fst y y ≫ y) y,
      U.ι ≫ M.1 = m.1 ∧
      IsIso (pullback.lift (f := y) (g := y) (pullback.fst y y) M.1 M.2.symm) ∧
      IsIso (pullback.lift (f := y) (g := y) M.1 (pullback.snd y y) (M.2.trans pullback.condition)) := by sorry
