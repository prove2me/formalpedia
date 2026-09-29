-- Prove2me | Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
-- name    : NumberField.IdeleClassGroup.isZero_H1_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/3fe657b7-b800-53d8-8e3e-c98514f76104
-- title:
--   Vanishing of H¹ of idele classes over a p-extension
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, let $p$ be a prime and assume the Galois group $G = \mathrm{Gal}(F/E)$, written `F ≃ₐ[E] F`, is a $p$-group. Let $D$ be a Galois descent datum for the ideles of $F$ over $E$, i.e. a monoid homomorphism from $G$ to the ring automorphisms of the adele ring `AdeleRing (𝓞 F) F` such that each $D(g)$ is continuous and agrees with $g$ on the image of $F$ under the structure map $F \to \mathbb{A}_F$. The idele class group `IdeleClassGroup (𝓞 F) F` is the quotient of $\mathbb{A}_F^\times$ by the subgroup of principal ideles, the image of $F^\times$ under the units map induced by $F \to \mathbb{A}_F$; $D$ induces on it, for each $g \in G$, the automorphism `D.classAct g` obtained from the automorphism of $\mathbb{A}_F^\times$ attached to $D(g)$. Assume given a multiplicative-distributive action of $G$ on this class group which coincides pointwise with $g \mapsto D.classAct\,g$. Then for every subgroup $S \le G$, the first group cohomology of $S$ acting on the idele class group, formed by restricting the associated $G$-representation along the inclusion of $S$, is a zero object.
--
--   This is Hilbert's Theorem 90 for idele classes, asserted simultaneously at every layer $F/F^S$ of a Galois $p$-extension. It is one of the inputs to the construction of a fundamental class for the idele class group of such an extension, and is used in the computation of the order of $H^2$ and in the verification of the generation conditions for that class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.isZero_H1_of_isPGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ S : Subgroup (F ≃ₐ[E] F), Limits.IsZero
      (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) := by sorry
