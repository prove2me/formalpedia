-- Prove2me | Theorems.Thm_NeronModelInfra_exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
-- name    : NeronModelInfra.exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/c1e08905-8cc0-5368-bbd6-7ee80e4992b5
-- title:
--   Strict birational group law yields a relative group law
-- statement:
--   Let $R$ be a discrete valuation ring (a domain with the discrete valuation ring structure) and let $y : Y \to \operatorname{Spec} R$ be a smooth, separated, locally of finite type and quasi-compact morphism of schemes. Let $U$ be an open subscheme of $Y \times_R Y =$ `pullback y y` and let $m$ be a morphism $U \to Y$ over $\operatorname{Spec} R$, i.e. a morphism whose composite with $y$ is the inclusion $U.\iota$ followed by $\mathrm{pr}_1$ followed by $y$. Assume: for each point $x$ of $Y$, the preimage of $U$ in the set-theoretic fibre of $\mathrm{pr}_1$ over $x$, and likewise in that of $\mathrm{pr}_2$, is dense; the morphism $\Phi = (U.\iota \circ \mathrm{pr}_1, m) : U \to Y \times_R Y$ obtained by `pullback.lift` is an open immersion, and the set-theoretic range of $\Phi$ meets every fibre of $\mathrm{pr}_1$ and every fibre of $\mathrm{pr}_2$ densely; the same three conditions hold for $\Psi = (m, U.\iota \circ \mathrm{pr}_2)$; and the associativity constraint: for every scheme $T$ with a morphism $t : T \to \operatorname{Spec} R$ and all four $T$-points $u, v, p, q$ of $U$ over $t$ such that $\mathrm{pr}_2 \circ u = \mathrm{pr}_1 \circ v$, $\mathrm{pr}_1 \circ p = m \circ u$, $\mathrm{pr}_2 \circ p = \mathrm{pr}_2 \circ v$, $\mathrm{pr}_1 \circ q = \mathrm{pr}_1 \circ u$ and $\mathrm{pr}_2 \circ q = m \circ v$, one has $m \circ p = m \circ q$. Assume further that $y$ admits a section $a$ with $a$ followed by $y$ the identity, and that there is an open subscheme $Y_0 \subseteq Y$ containing every point $p$ of $Y$ with no proper generisation in its fibre (every $p'$ with $p' \rightsquigarrow p$ and $y(p') = y(p)$ equals $p$), such that every point $q$ of $Y \times_R Y$ with both projections in $Y_0$ lies in $U$. Then there exists a `RelativeGroupLaw R y`, that is, a multiplication, unit and inverse on the $T$-points of $y$ over $\operatorname{Spec} R$ for all $T$, satisfying associativity, the two unit laws and left inverse, and natural under base change $\psi$, whose multiplication extends $m$ in the following sense: for every $T$, every $t : T \to \operatorname{Spec} R$, every $T$-point $w$ of $U$ over $t$ and all $T$-points $b, c, d$ of $Y$ over $t$ with $b = \mathrm{pr}_1 \circ U.\iota \circ w$, $c = \mathrm{pr}_2 \circ U.\iota \circ w$ and $d = m \circ w$, one has $L.\mathrm{mul}\ t\ b\ c = d$.
--
--   This is the functor-of-points form of the statement that a smooth separated $R$-scheme of finite type with a section, carrying a strict birational group law defined on the square of an $R$-dense open subscheme, is a group scheme for that law (Bosch–Lütkebohmert–Raynaud, 5.3, Lemma 8). It is the step that converts the birational group law produced from the Jacobian of a curve with good reduction into an honest relative group law, and is used in the construction of the group structure on the smooth model via Hensel's lemma.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem NeronModelInfra.exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
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
    ∃ L : RelativeGroupLaw R y,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : SchemeHomOver t (U.ι ≫ pullback.fst y y ≫ y))
        (b c d : SchemeHomOver t y),
        b.1 = w.1 ≫ U.ι ≫ pullback.fst y y → c.1 = w.1 ≫ U.ι ≫ pullback.snd y y → d.1 = w.1 ≫ m.1 →
        L.mul t b c = d := by sorry
