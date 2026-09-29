-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/caf2914b-bbf0-54ff-bbca-01be8cb31495
-- title:
--   Multiplication by n is a torsor under the representing n-torsion scheme
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f\colon A\to\operatorname{Spec}R$ a morphism, and let $L$ be a relative group law for $f$: an assignment, to each $R$-scheme $t\colon T\to\operatorname{Spec}R$, of a multiplication, a unit and an inverse on the set of $T$-points of $A$ over $t$ (morphisms $\varphi\colon T\to A$ with $\varphi$ followed by $f$ equal to $t$), satisfying associativity, the two unit laws and left inverses, and natural in $T$ under precomposition with morphisms $\psi\colon T'\to T$ over $\operatorname{Spec}R$. Assume $L$ is commutative, i.e. the multiplication on $T$-points is commutative for every $R$-scheme $T$. Let $n\in\mathbb{N}$, let $s\colon S\to\operatorname{Spec}R$ be an $R$-scheme and $u$ an $S$-point of $A$ over $s$ which is $n$-torsion, in the sense that the $n$-fold iterate $\mathrm{nsmul}$ of multiplication by $u$ applied to the unit equals the unit $S$-point; assume further that $(S,u)$ is universal for this property: for every $R$-scheme $t\colon T\to\operatorname{Spec}R$ and every $n$-torsion $T$-point $z$ of $A$ over $t$, there is a unique $g\colon T\to S$ with $g$ followed by $u$ equal to $z$. The conclusion asserts the existence of a morphism $\mathrm{act}\colon A\times_{\operatorname{Spec}R}S\to A$ (the pullback of $f$ along $s$) such that: $\mathrm{act}$ followed by $f$ equals the first projection followed by $f$; for every $R$-scheme $t\colon T\to\operatorname{Spec}R$, every $T$-point $x$ of $A$ over $t$ and every $g\colon T\to S$ with $x$ followed by $f$ equal to $g$ followed by $s$, the induced map $T\to A\times_{\operatorname{Spec}R}S$ followed by $\mathrm{act}$ is the $L$-product of $x$ with the $T$-point $g$ followed by $u$; and, writing $[n]=L.\mathrm{schemeNsmul}\,n$ for the endomorphism of $A$ obtained by applying the $n$-fold multiplication to the identity point of $A$, there is an identity $\mathrm{pr}_1\circ[n]$-wise, namely the first projection followed by $[n]$ equals $\mathrm{act}$ followed by $[n]$, such that the resulting morphism $A\times_{\operatorname{Spec}R}S\to A\times_{[n],A,[n]}A$ with components the first projection and $\mathrm{act}$ is an isomorphism.
--
--   This is the statement that multiplication by $n$ on $A$ is a torsor under any scheme representing the $n$-torsion: the shear map $(\mathrm{pr}_1,\mathrm{act})$ identifies $A\times_{\operatorname{Spec}R}S$ with the fibre product of $[n]$ with itself. It is the general-base-ring version of the corresponding statement over a field, and is used in the treatment of polarisations, where a translation by a $2$-torsion point is compared with the pullback along $[2]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint_of_commRing
    (R : Type u) [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (u : SchemeHomOver s f) (hu : L.IsTorsionPoint s n u)
    (huniv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (z : SchemeHomOver t f),
      L.IsTorsionPoint t n z → ∃! g : T ⟶ S, g ≫ u.1 = z.1) :
    ∃ (act : pullback f s ⟶ A),
      act ≫ f = pullback.fst f s ≫ f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (g : T ⟶ S)
          (hx : x.1 ≫ f = g ≫ s),
        pullback.lift x.1 g hx ≫ act =
          (L.mul t x ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩).1) ∧
      ∃ (hsh : pullback.fst f s ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n),
        IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n) (pullback.fst f s) act hsh) := by sorry
