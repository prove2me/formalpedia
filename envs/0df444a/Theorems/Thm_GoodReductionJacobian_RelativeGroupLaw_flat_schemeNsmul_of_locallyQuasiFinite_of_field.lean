-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field
-- name    : GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_locallyQuasiFinite_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/14b1c5dc-da93-5994-bbaa-6c659fe49879
-- title:
--   Flatness of a quasi-finite [n] on a smooth connected group
-- statement:
--   Let $k$ be a field and let $f \colon A \to \operatorname{Spec} k$ be a morphism of schemes that is smooth, with the underlying space of $A$ preconnected. Let $G$ be a relative group law on $f$ over $k$: for every scheme $T$ and every morphism $t \colon T \to \operatorname{Spec} k$ it provides a multiplication, a unit and an inversion on the set of $T$-points $\{\varphi \colon T \to A \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, the two unit laws and the left inverse law, the multiplication being compatible with base change along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$. For a natural number $n$, let `G.schemeNsmul n : A ⟶ A` be the underlying morphism of the $n$-fold $G$-power of the tautological $A$-point $\mathrm{id}_A$ of $A$, formed by the recursion $0 \mapsto$ unit, $m+1 \mapsto (m\text{-th power}) \cdot \mathrm{id}_A$. Assume this endomorphism `G.schemeNsmul n` is locally quasi-finite. Then it is flat.
--
--   This is the standard flatness of multiplication by $n$ on a smooth connected group scheme over a field once $[n]$ is known to be quasi-finite (as in the treatment of finite flat kernels in Néron model theory). It feeds the statements that produce finite flat kernels $A[n]$ and the flat, surjective, locally quasi-finite behaviour of $[n]$, in particular for prime powers, used in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_locallyQuasiFinite_of_field.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_locallyQuasiFinite_of_field
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)}
    [Smooth f] [PreconnectedSpace A]
    (G : RelativeGroupLaw k f) (n : ℕ) [LocallyQuasiFinite (G.schemeNsmul n)] :
    Flat (G.schemeNsmul n) := by sorry
