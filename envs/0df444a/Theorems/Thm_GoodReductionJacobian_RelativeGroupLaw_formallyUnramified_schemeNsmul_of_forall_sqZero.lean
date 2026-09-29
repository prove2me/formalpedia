-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero
-- name    : GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/13a33a53-8e3d-529a-a1f5-ebedf9e458ef
-- title:
--   Formal unramifiedness of [n] via square-zero torsion vanishing
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f \colon A \to \operatorname{Spec} R$ a morphism, and let $G$ be a relative group law on $f$: for every scheme $T$ and every $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inversion on the set $\mathrm{SchemeHomOver}\ t\ f$ of morphisms $T \to A$ whose composite with $f$ is $t$, satisfying associativity, both unit laws, left inversion, and naturality of the multiplication under precomposition with any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Assume the multiplication is commutative on the points over every base $t$, and let $n \in \mathbb{N}$. Assume further that for all commutative rings $R', S'$, every surjective ring homomorphism $\varphi \colon R' \to S'$ whose kernel satisfies $(\ker \varphi)^2 = 0$, every $t \colon \operatorname{Spec} R' \to \operatorname{Spec} R$ and every $k \colon \operatorname{Spec} R' \to A$ over $t$: if the composite of $\operatorname{Spec} \varphi$ with $k$ is the unit point over $\operatorname{Spec}\varphi$ followed by $t$, and the $n$-fold iterate $G.\mathtt{nsmul}\ t\ n\ k$ (defined by $0 \mapsto$ unit, $m+1 \mapsto$ product of the $m$-th iterate with $k$) is the unit point, then $k$ is the unit point. Then the morphism $A \to A$ underlying the $n$-fold iterate of the tautological point $\mathrm{id}_A$ over $f$, that is $G.\mathtt{schemeNsmul}\ n$, is formally unramified.
--
--   This is the infinitesimal step in the standard proof that multiplication by $n$ on a commutative group scheme is unramified as soon as the $n$-torsion in square-zero deformations of the unit section is trivial. It is used to obtain formal unramifiedness, and then local quasi-finiteness, of $[n]$ when $n$ is invertible on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_forall_sqZero.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_forall_sqZero
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ)
    (hTF : ∀ (R' S' : CommRingCat.{u}) (φ : R' ⟶ S'), Function.Surjective φ →
      RingHom.ker φ.hom ^ 2 = ⊥ →
      ∀ (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f),
        schemeHomOverComp (Spec.map φ) rfl k = G.one (Spec.map φ ≫ t) →
        G.nsmul t n k = G.one t → k = G.one t) :
    FormallyUnramified (G.schemeNsmul n) := by sorry
