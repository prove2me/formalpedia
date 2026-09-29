-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective
-- name    : GoodReductionJacobian.RelativeGroupLaw.isSeparated_and_quasiCompact_of_isPullback_action_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/c7fb3bd7-5471-56f4-878b-d3781b453706
-- title:
--   Separatedness and quasi-compactness of an fppf quotient
-- statement:
--   Let $k$ be a field and let $f : G \to \operatorname{Spec} k$ be a morphism of schemes that is separated and quasi-compact, equipped with a relative group law $L$ over $k$: for every scheme $T$ with a structure morphism $t : T \to \operatorname{Spec} k$, a multiplication, a unit and an inverse on the set of morphisms $T \to G$ over $t$ (pairs $(\varphi, \varphi \circ f = t)$), satisfying associativity, the two unit laws and left inverses, and with the multiplication compatible with base change along any $\psi : T' \to T$ over $k$. Let $i : N \to G$ be a closed immersion, and let $fQ : Q \to \operatorname{Spec} k$ and $q : G \to Q$ be morphisms with $q$ followed by $fQ$ equal to $f$, where $q$ is flat, locally of finite presentation, quasi-compact and surjective. Assume that the square formed by the second projection $\mathrm{pr}_2 : N \times_{\operatorname{Spec} k} G \to G$ (the pullback of $i$ followed by $f$ against $f$) and by $L$'s action morphism $L.action\ i$, which sends a point $(n, g)$ to the product $i(n) \cdot g$ computed in the group law on points over $\mathrm{pr}_2$ followed by $f$, together with $q$ on both remaining sides, is a pullback square; in particular $\mathrm{pr}_2$ followed by $q$ equals $L.action\ i$ followed by $q$. Then $fQ$ is separated and quasi-compact.
--
--   This records that an effective fppf quotient of a separated quasi-compact $k$-group-like scheme by the action of a closed subscheme is again separated and quasi-compact over $k$, the separatedness being obtained by fppf descent of the closed immersion $(\mathrm{pr}_2, \text{action}) : N \times_k G \to G \times_k G$ along the cover $q \times q$. It is used in the construction of such a quotient, [`GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_fppf_quotient_isPullback_action_of_isClosedImmersion).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isSeparated_and_quasiCompact_of_isPullback_action_of_surjective.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isSeparated_and_quasiCompact_of_isPullback_action_of_surjective
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [QuasiCompact q] [Surjective q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    IsSeparated fQ ∧ QuasiCompact fQ := by sorry
