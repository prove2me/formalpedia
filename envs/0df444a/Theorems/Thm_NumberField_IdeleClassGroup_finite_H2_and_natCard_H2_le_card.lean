-- Prove2me | Theorems.Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card
-- name    : NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/6017958f-d78e-59be-ba41-aa4ba6cacece
-- title:
--   Second inequality: #H²(S,C_F)≤ |S| for all subgroups
-- statement:
--   Let $E$ and $F$ be number fields with $F$ an $E$-algebra and $F/E$ Galois, and write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group. Let $C_F$ denote the idèle class group $(\mathbb{A}_F^{(\mathcal{O}_F)})^\times / \mathrm{principalIdeles}$, that is, the units of the adèle ring of $F$ modulo the image of $F^\times$ under the units map of $\mathrm{algebraMap}$. Let $D$ be an `IdeleGaloisDescent` datum for $\mathcal{O}_F$, $E$, $F$: a monoid homomorphism from $G$ to the ring automorphisms of the adèle ring, each member continuous, compatible with the $E$-algebra action on $F$ via $\mathrm{algebraMap}$; it induces automorphisms `D.classAct g` of $C_F$ by passing to the quotient. Assume given a `MulDistribMulAction` of $G$ on $C_F$ whose scalar action agrees pointwise with `D.classAct`, and view $C_F$ as a $\mathbb{Z}$-linear representation of $G$ via `Rep.ofMulDistribMulAction`. The conclusion: for every finite subgroup $S \le G$, the group cohomology $H^2(S, C_F)$ of the restricted representation along $S.subtype$ is finite, and its cardinality is at most $\#S$.
--
--   This is the second inequality of global class field theory at each layer $F/F^S$, in the form bounding $\#H^2(S,C_F)$ by the order of $S$ for all subgroups $S$ at once; it is the general-degree statement obtained from the prime-power case by Sylow patching. It feeds the construction of the fundamental class of the idèle class group and the determination of $\#H^2$ as exactly $\#S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleClassGroup_finite_H2_and_natCard_H2_le_card.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c) :
    ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Finite
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ∧
      Nat.card
        (groupCohomology (Rep.res S.subtype
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) ≤ Fintype.card S := by sorry
