-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_stalk_one_of_charZero
-- name    : GoodReductionJacobian.RelativeGroupLaw.isReduced_stalk_one_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/5b974f58-8a80-5332-b73a-7ce8a696236e
-- title:
--   Reducedness of the stalk at the unit (Cartier)
-- statement:
--   Let $k$ be a field of characteristic zero, let $G$ be a scheme, and let $g : G \to \operatorname{Spec} k$ be a morphism that is locally of finite type. Let $L$ be a relative group law on $g$ in the sense of the structure `RelativeGroupLaw`: for every scheme $T$ and every morphism $t : T \to \operatorname{Spec} k$ it provides operations `mul`, `one`, `inv` on the set of pairs $(\varphi : T \to G)$ with $\varphi$ followed by $g$ equal to $t$, together with associativity of `mul`, the two unit laws for `one`, the left inverse law $\mathrm{inv}(x)\cdot x = \mathrm{one}$, and naturality of `mul` along any $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$ (the induced map being precomposition with $\psi$). Taking $T = \operatorname{Spec} k$ and $t$ the identity, the unit $\mathrm{one}$ is a section $\operatorname{Spec} k \to G$; let $e \in G$ be the image of the closed point of $\operatorname{Spec} k$ under its underlying map of topological spaces. The conclusion is that the local ring $\mathcal O_{G,e}$, the stalk of the structure presheaf of $G$ at $e$, is reduced, i.e. its only nilpotent element is $0$.
--
--   This is the local form at the unit point of Cartier's theorem that a group scheme locally of finite type over a field of characteristic zero is reduced (hence smooth). It feeds the global statement [`GoodReductionJacobian.RelativeGroupLaw.isReduced_of_charZero`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isReduced_of_charZero), used in the treatment of good reduction of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_stalk_one_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.isReduced_stalk_one_of_charZero
    (k : Type) [Field k] [CharZero k] {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (L : RelativeGroupLaw k g) :
    _root_.IsReduced (G.presheaf.stalk ((L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k))) := by sorry
