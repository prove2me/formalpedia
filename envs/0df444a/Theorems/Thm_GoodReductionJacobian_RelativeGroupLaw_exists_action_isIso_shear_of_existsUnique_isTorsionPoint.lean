-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/288a37d4-2480-5efb-8267-54495837f922
-- title:
--   Torsor structure under a scheme representing the n-torsion
-- statement:
--   Let $K$ be a field and $f \colon A \to \operatorname{Spec} K$ a scheme over $K$, and let $L$ be a relative group law on $f$, that is, a functorial group structure on the sets $\mathrm{SchemeHomOver}\,t\,f = \{\varphi \colon T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over $K$, compatible with base change along morphisms of $K$-schemes; assume $L$ is commutative, i.e. $L.\mathrm{mul}$ is commutative on the points of every $K$-scheme. Fix $n \in \mathbb{N}$, a $K$-scheme $s \colon S \to \operatorname{Spec} K$ and an $S$-point $u$ of $A$ over $K$ which is $n$-torsion, meaning that the $n$-fold $L$-product of $u$ with itself is the identity point $L.\mathrm{one}\,s$. Assume $(S,u)$ is universal for this property: for every $K$-scheme $t \colon T \to \operatorname{Spec} K$ and every $n$-torsion $T$-point $z$ of $A$ there is a unique $g \colon T \to S$ with $g$ followed by $u$ equal to $z$. Then there is a morphism $\mathrm{act} \colon A \times_{\operatorname{Spec} K} S \to A$ such that: (i) $\mathrm{act}$ followed by $f$ equals the first projection followed by $f$, so $\mathrm{act}$ is a morphism of $K$-schemes; (ii) on points, for every $K$-scheme $t \colon T \to \operatorname{Spec} K$, every $T$-point $x$ of $A$ over $K$ and every $g \colon T \to S$ with $x$ followed by $f$ equal to $g$ followed by $s$, the morphism $T \to A \times_{\operatorname{Spec} K} S$ determined by $x$ and $g$, followed by $\mathrm{act}$, is the $L$-product of $x$ with the $T$-point $g$ followed by $u$; and (iii) the resulting equality of $\mathrm{pr}_1$ followed by $[n] = L.\mathrm{schemeNsmul}\,n$ (the first component of the $n$-fold $L$-product of the identity point of $A$ with itself) and $\mathrm{act}$ followed by $[n]$ holds, and the induced shear morphism $(\mathrm{pr}_1, \mathrm{act}) \colon A \times_{\operatorname{Spec} K} S \to A \times_{[n],A,[n]} A$ is an isomorphism.
--
--   This is the statement that a commutative group scheme over $K$ is a torsor under any scheme representing its $n$-torsion, relative to multiplication by $n$: translation by the universal $n$-torsion point gives an action whose shear map onto the fibre product of $[n]$ with itself is an isomorphism. It is used in the form where the $n$-torsion is given by an equivalence of point functors, in [`GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_torsion_points_equiv), as an input to the study of $[n]$ on Jacobians with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_action_isIso_shear_of_existsUnique_isTorsionPoint.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_action_isIso_shear_of_existsUnique_isTorsionPoint
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (n : ℕ)
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (u : SchemeHomOver s f) (hu : L.IsTorsionPoint s n u)
    (huniv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (z : SchemeHomOver t f),
      L.IsTorsionPoint t n z → ∃! g : T ⟶ S, g ≫ u.1 = z.1) :
    ∃ (act : pullback f s ⟶ A),
      act ≫ f = pullback.fst f s ≫ f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (g : T ⟶ S)
          (hx : x.1 ≫ f = g ≫ s),
        pullback.lift x.1 g hx ≫ act =
          (L.mul t x ⟨g ≫ u.1, by rw [Category.assoc, u.2, ← hx, x.2]⟩).1) ∧
      ∃ (hsh : pullback.fst f s ≫ L.schemeNsmul n = act ≫ L.schemeNsmul n),
        IsIso (pullback.lift (f := L.schemeNsmul n) (g := L.schemeNsmul n) (pullback.fst f s) act hsh) := by sorry
