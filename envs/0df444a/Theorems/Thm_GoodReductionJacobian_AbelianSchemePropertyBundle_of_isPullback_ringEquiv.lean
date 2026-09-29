-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_ringEquiv
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/b207679f-44e4-56ec-817a-105570dcfa23
-- title:
--   Abelian-scheme property bundle along a pullback over a field isomorphism
-- statement:
--   Let $k$ and $k'$ be fields in a fixed universe and let $e \colon k \xrightarrow{\ \sim\ } k'$ be a ring isomorphism. Let $X$ and $X'$ be schemes with structure morphisms $f \colon X \to \operatorname{Spec} k$ and $f' \colon X' \to \operatorname{Spec} k'$, and let $i \colon X' \to X$ be a morphism such that the square formed by $i$, $f'$, $f$ and $\operatorname{Spec}$ of the ring homomorphism underlying $e$ is cartesian, i.e. $i$ followed by $f$ equals $f'$ followed by $\operatorname{Spec}(e)$ and the square is a pullback. Assume further given a relative group law $L'$ on $f'$, that is, functorially compatible multiplication, unit and inverse operations on the sets $\{\varphi \colon T \to X' \mid \varphi \text{ followed by } f' = t\}$ of $T$-points over each $t \colon T \to \operatorname{Spec} k'$, satisfying associativity, both unit laws, the left inverse law and naturality under precomposition with morphisms $T' \to T$ over $\operatorname{Spec} k'$. Assume finally that $f$ carries the abelian-scheme property bundle over $k$: $f$ is smooth, $f$ is proper, the preimage under the underlying continuous map of $f$ of every point of $\operatorname{Spec} k$ is a connected (in particular nonempty) subspace, and a relative group law on $f$ exists. Then $f'$ carries the abelian-scheme property bundle over $k'$.
--
--   This records that the package of conditions defining an abelian scheme over a field — smoothness, properness, connected fibres and the existence of a relative group law — is transported along a cartesian square whose base morphism is $\operatorname{Spec}$ of a field isomorphism, the shape in which it is needed when an abelian scheme is transported across an identification of residue fields. It is used in the construction of fake elliptic curves and their deformations over algebraically closed fields of positive characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback_ringEquiv.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.of_isPullback_ringEquiv
    {k k' : Type u} [Field k] [Field k'] (e : k ≃+* k')
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k'))
    (i : X' ⟶ X) (hi : IsPullback i f' f (Spec.map (CommRingCat.ofHom e.toRingHom)))
    (L' : RelativeGroupLaw k' f') (hA : AbelianSchemePropertyBundle k f) :
    AbelianSchemePropertyBundle k' f' := by sorry
