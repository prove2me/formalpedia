-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
-- name    : GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/49114277-a680-592e-b5f3-5c87d5e7a087
-- title:
--   Multiplication by n on an abelian variety: degree n^{2g}
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme and $f \colon A \to \operatorname{Spec} K$ a morphism, and let $L$ be a relative group law for $f$ over $K$: functorially in a $K$-scheme $t \colon T \to \operatorname{Spec} K$, a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the set of $T$-points $\{\varphi \colon T \to A \mid \varphi \circ f = t\}$, the multiplication commuting with base change along morphisms $\psi \colon T' \to T$ over $\operatorname{Spec} K$. Assume $L$ is commutative, i.e. all these group structures are abelian, and assume the bundle of properties `AbelianSchemePropertyBundle` for $f$: $f$ is smooth, proper, every fibre of the underlying map of $f$ over a point of $\operatorname{Spec} K$ is connected, and $f$ admits a relative group law. Assume further that $f$ is smooth of relative dimension $g$, and let $n \neq 0$ be a natural number. Write $[n] =$ `L.schemeNsmul n` for the underlying morphism $A \to A$ of the $n$-fold $L$-product of the identity $T$-point $\mathrm{id}_A$ taken in the group of $A$-points of $f$, and let $A[n] \to \operatorname{Spec} K$ be the second projection from the fibre product of $[n]$ with the unit section of $L$ over $\operatorname{Spec} K$. Then: $A[n] \to \operatorname{Spec} K$ is a finite morphism, its rank at the closed point of $\operatorname{Spec} K$ is $n^{2g}$; and $[n]$ is finite, flat, surjective on underlying points, with rank $n^{2g}$ at every point $x$ of $A$.
--
--   This is the standard statement, valid in every characteristic, that multiplication by a nonzero integer $n$ on a $g$-dimensional abelian variety is a finite flat surjective morphism of degree $n^{2g}$, and correspondingly that the $n$-torsion subgroup scheme $A[n]$ is finite of order $n^{2g}$ over the base. It is packaged for consumers that need ranks of finite flat morphisms, and is cited in the treatment of polarisations and stabilisers of two-torsion kernels, and in the construction of extra level structures on fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.isFinite_schemeKerStr_and_finrank_eq_pow_and_finrank_schemeNsmul_eq_pow
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : n ≠ 0) :
    IsFinite (L.schemeKerStr n) ∧
      (L.schemeKerStr n).finrank (IsLocalRing.closedPoint K) = n ^ (2 * g) ∧
      IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n) ∧
      Function.Surjective (L.schemeNsmul n) ∧
      ∀ x : A, (L.schemeNsmul n).finrank x = n ^ (2 * g) := by sorry
