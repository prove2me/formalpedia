-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective
-- name    : GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isPullback_action_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/eefa2625-d217-58d0-8d2d-cddd7d399efc
-- title:
--   Smoothness and dimension for an effective quotient by a smooth subscheme
-- statement:
--   Let $k$ be a field and let $f : G \to \operatorname{Spec} k$ be a morphism of schemes equipped with a relative group law $L$, that is, a system of group structures on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of $T$-points of $G$ over each $t : T \to \operatorname{Spec} k$, natural in $T$. Assume $f$ is smooth of relative dimension $g$. Let $i : N \to G$ be a closed immersion with $N$ non-empty such that $f \circ i$ is smooth of relative dimension $h$. Let $fQ : Q \to \operatorname{Spec} k$ and $q : G \to Q$ satisfy $fQ \circ q = f$, with $q$ flat, locally of finite presentation, surjective and quasi-compact. Assume finally that the square formed by the two morphisms $\mathrm{pr}_2 =$ `pullback.snd` $(f \circ i, f)$ and `L.action i` from $N \times_{\operatorname{Spec} k} G$ to $G$, together with $q$ and $q$, is a pullback square; here `L.action i` is the morphism whose associated point over $\mathrm{pr}_2 \circ f$ is the $L$-product of $i \circ \mathrm{pr}_1$ and $\mathrm{pr}_2$, i.e. the action $(n,x) \mapsto n\cdot x$. The conclusion is that $q$ is smooth of relative dimension $h$, that $fQ$ is smooth of relative dimension $g - h$ (truncated subtraction of naturals), and that $h \le g$.
--
--   This is the descent step in the construction of a quotient of a smooth group scheme over a field by a smooth closed subgroup scheme: given a morphism $q$ that is an effective fppf quotient for the action groupoid, it records that $q$ itself is smooth of relative dimension $h$ and that the quotient is smooth of relative dimension $g - h$. It is used in the existence statement [`GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_quotient_smoothOfRelativeDimension_sub_of_isClosedImmersion_of_isAlgClosed) over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isPullback_action_of_surjective.lean

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

theorem GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isPullback_action_of_surjective
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} [Nonempty N] (i : N ⟶ G) [IsClosedImmersion i] (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (q : G ⟶ Q) (hq : q ≫ fQ = f)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q] [QuasiCompact q]
    (hR : IsPullback (CategoryTheory.Limits.pullback.snd (i ≫ f) f) (L.action i) q q) :
    SmoothOfRelativeDimension h q ∧ SmoothOfRelativeDimension (g - h) fQ ∧ h ≤ g := by sorry
