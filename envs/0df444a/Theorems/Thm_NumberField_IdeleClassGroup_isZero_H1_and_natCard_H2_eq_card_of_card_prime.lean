-- Prove2me | Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime
-- name    : NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/1d64c58f-a512-577e-81b6-0c22f21b62e0
-- title:
--   H¹ vanishes and #H² = #S for idele classes at prime-order S
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, and write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group. Let $D$ be an idele Galois descent datum for $\mathcal{O}_F$ over $E$ and $F$: a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $G$ to the ring automorphisms of the adele ring $\mathrm{AdeleRing}\,(\mathcal{O}_F)\,F$, each $D.\mathrm{act}\,g$ continuous and compatible with the structure map of $F$ in the sense that $D.\mathrm{act}\,g\,(\iota x) = \iota(g x)$ for all $x \in F$. Here the idele class group $\mathrm{IdeleClassGroup}\,(\mathcal{O}_F)\,F$ is the quotient of the unit group of the adele ring by the subgroup of principal ideles, namely the image of $F^{\times}$ under the map induced by $\iota$. Assume $G$ acts on this quotient by group automorphisms (a `MulDistribMulAction`), and that the action is pinned to $D$: $g \bullet c = D.\mathrm{classAct}\,g\,c$ for all $g \in G$ and all classes $c$, where $D.\mathrm{classAct}\,g$ is the automorphism of the quotient induced by $u \mapsto D.\mathrm{act}\,g\,u$ on units. Let $S \le G$ be a finite subgroup whose order $\#S$ is prime. Then, for the $\mathbb{Z}$-linear representation attached to this action, restricted along the inclusion $S \hookrightarrow G$, the degree-$1$ group cohomology is a zero object, and the degree-$2$ group cohomology has cardinality exactly $\#S$.
--
--   This is the prime-order case of the two cohomological axioms of a class formation for idele class groups: Hilbert's Theorem 90 for idele classes of a cyclic extension of prime degree, together with the exact determination of the order of $H^2$. It feeds the treatment of $p$-groups and of general cyclic subgroups, being cited by [`NumberField.IdeleClassGroup.isZero_H1_of_isPGroup`](thm.html#NumberField.IdeleClassGroup.isZero_H1_of_isPGroup), [`NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup`](thm.html#NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup) and [`NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_isCyclic`](thm.html#NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_isCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleClassGroup_isZero_H1_and_natCard_H2_eq_card_of_card_prime.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_card_prime
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (S : Subgroup (F ≃ₐ[E] F)) [Fintype S] (hS : (Fintype.card S).Prime) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 1) ∧
      Nat.card (groupCohomology (Rep.res S.subtype
        (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S := by sorry
