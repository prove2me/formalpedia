-- Prove2me | Theorems.Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup
-- name    : NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/bf7485d0-519e-5679-88c5-dc1e57b1738d
-- title:
--   Finiteness and order bound for H²(S,C_F) in a p-extension
-- statement:
--   Let $E$ and $F$ be number fields (types in `Type`) with $F$ an algebra over $E$ and $F/E$ Galois, let $p$ be a prime and suppose the Galois group $F \simeq_{alg[E]} F$ is a $p$-group in the sense of `IsPGroup p`. Let $D$ be an idèle Galois descent datum for $\mathcal{O}_F$ over $E$ and $F$: a monoid homomorphism from $F \simeq_{alg[E]} F$ to the ring automorphisms of the adèle ring $\mathrm{AdeleRing}(\mathcal{O}_F, F)$, each automorphism continuous, compatible with the structure map $F \to \mathrm{AdeleRing}(\mathcal{O}_F,F)$ in the sense that $D.\mathrm{act}\,g$ sends the image of $x \in F$ to the image of $g x$. Suppose the Galois group acts multiplicatively and distributively on the idèle class group $\mathrm{IdeleClassGroup}(\mathcal{O}_F,F) = \mathrm{AdeleRing}(\mathcal{O}_F,F)^\times / F^\times$, where $F^\times$ denotes the subgroup `principalIdeles` of principal idèles, i.e. the range of the unit map induced by $F \to \mathrm{AdeleRing}(\mathcal{O}_F,F)$, and assume this action agrees pointwise with the automorphism $D.\mathrm{classAct}\,g$ that $D$ induces on the quotient. The conclusion is that for every subgroup $S$ of the Galois group carrying a `Fintype` structure, the degree-$2$ group cohomology of the $\mathbb{Z}$-linear representation attached to this action, restricted along the inclusion of $S$, is finite, and its cardinality is at most the cardinality of $S$.
--
--   This is the upper bound half of the second inequality of class field theory, asserted at every layer $F/F^{S}$ of a Galois $p$-extension; the classical statement is the equality $\#H^2(S,C_F)=\#S$, of which only the inequality (together with finiteness) is asserted here. It is used in the construction of the fundamental class for the idèle class group of a $p$-extension and in the results establishing the corresponding equality and generation statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card_of_isPGroup.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (F ≃ₐ[E] F))
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Finite
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ∧
      Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ≤ Fintype.card S := by sorry
