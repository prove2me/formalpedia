-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_isReduced_stalk_one_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.isReduced_of_isReduced_stalk_one_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/658458ea-3314-5c47-ae64-cd3608c9cf23
-- title:
--   Homogeneity: reducedness at the unit gives reducedness of G
-- statement:
--   Let $k$ be an algebraically closed field, let $G$ be a scheme and let $g : G \to \operatorname{Spec} k$ be a morphism that is locally of finite type. Let $L$ be a relative group law on $g$ in the sense of `RelativeGroupLaw`: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} k$, a multiplication, a unit and an inversion on the set of $T$-points of $G$ over $t$, i.e. on pairs $(\varphi : T \to G)$ with $\varphi$ followed by $g$ equal to $t$, satisfying associativity, the two unit laws and left inverse cancellation, and with multiplication compatible with base change along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$. Taking $T = \operatorname{Spec} k$ with $t$ the identity, the unit $L.\mathrm{one}$ provides a section $e : \operatorname{Spec} k \to G$ of $g$; write $e(\mathfrak{m})$ for the image under $e$ of the closed point of $\operatorname{Spec} k$. The hypothesis is that the local ring $\mathcal{O}_{G, e(\mathfrak{m})}$, the stalk of the structure presheaf of $G$ at that point, is reduced. The conclusion is that the scheme $G$ is reduced.
--
--   This is the homogeneity principle for group schemes locally of finite type over an algebraically closed field: reducedness at the unit point propagates to the whole scheme by translation. It is used in the treatment of good reduction of Jacobians, and is invoked by [`GoodReductionJacobian.RelativeGroupLaw.isReduced_of_charZero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isReduced_of_charZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_of_isReduced_stalk_one_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_of_isReduced_stalk_one_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g)
    (he : _root_.IsReduced (G.presheaf.stalk ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k)))) :
    IsReduced G := by sorry
