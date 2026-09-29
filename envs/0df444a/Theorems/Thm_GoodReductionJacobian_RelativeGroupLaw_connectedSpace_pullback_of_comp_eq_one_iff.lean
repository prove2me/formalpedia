-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff
-- name    : GoodReductionJacobian.RelativeGroupLaw.connectedSpace_pullback_of_comp_eq_one_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/a567d931-6df3-5f76-ae47-8e8e8ab93fa3
-- title:
--   Connectedness of the pullback of a connected closed subscheme
-- statement:
--   Let $k$ be a field, let $f : G \to \operatorname{Spec} k$ be a $k$-scheme, and let $L$ be a relative group law on $f$: that is, for every $k$-scheme $t : T \to \operatorname{Spec} k$ a multiplication, unit and inversion on the set of morphisms $T \to G$ over $\operatorname{Spec} k$, satisfying associativity, the unit laws and left inverses, and compatible with base change along any $\psi : T' \to T$ over $\operatorname{Spec} k$. Let $i : N \to G$ be a closed immersion, let $f_Q : Q \to \operatorname{Spec} k$ carry a relative group law $L_Q$, and let $q$ be a morphism $G \to Q$ with $q \circ$ (the structure map $f_Q$) $= f$, such that: composition with $q$ is multiplicative on $T$-points for every $k$-scheme $T$ (hypothesis `hq`); and, for every $k$-scheme $t : T \to \operatorname{Spec} k$, a $T$-point $x$ of $G$ over $\operatorname{Spec} k$ composes with $q$ to the unit of $L_Q$ if and only if $x$ factors as some $T$-point of $N$ followed by $i$ (hypothesis `hker`). Assume further that $N$ is affine, that $i$ followed by $f$ is geometrically connected, that $q$ is smooth of some relative dimension $h$, surjective and quasi-compact, and that $j : M \to Q$ is a closed immersion whose source has connected underlying space. Then the underlying topological space of the fibre product $G \times_Q M$ of $q$ and $j$ is connected.
--
--   This is the connectedness step in the Chevalley-type construction of a quotient: the preimage of a connected closed subscheme under a surjective smooth homomorphism with affine geometrically connected kernel is again connected. It is used in producing an affine closed subscheme of $G$ from one of $Q$, in the construction of Néron models for Jacobians of curves with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_connectedSpace_pullback_of_comp_eq_one_iff.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.connectedSpace_pullback_of_comp_eq_one_iff
    (k : Type u) [Field k]
    {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ)
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    [IsAffine N] [GeometricallyConnected (i ≫ f)]
    (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1] [QuasiCompact q.1]
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [ConnectedSpace M] :
    ConnectedSpace ↥(pullback q.1 j) := by sorry
