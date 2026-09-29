-- Prove2me | Theorems.Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_fixedField
-- name    : NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_fixedField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/e51ebf2c-b55a-5196-a2e3-d7b3ea83d8c5
-- title:
--   Galois descent for idele classes: C_F^N ≅ C_{F^N}
-- statement:
--   Let $E \subseteq F$ be number fields with $F/E$ Galois, write $G = F \simeq_{\mathrm{alg}[E]} F$ for its Galois group, and let $C_F$ denote the idele class group $(\mathbb{A}_{F})^{\times}/F^{\times}$ of $F$, i.e. the quotient of the units of `AdeleRing (𝓞 F) F` by the image of $F^{\times}$ under the unit map of the structure morphism. Given a Galois descent datum $D$ for the ideles of $F$ over $E$ — a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_F$, each automorphism continuous and compatible with the embedding of $F$ — and a multiplicative distributive action of $G$ on $C_F$ whose action agrees with the automorphism `D.classAct g` induced by $D$ on the quotient (hypothesis `hact`), let $N$ be a normal subgroup of $G$ and $K =$ `IntermediateField.fixedField N`. Assume given likewise a descent datum $D_2$ for the ideles of $K$ over $E$ and an action of $K \simeq_{\mathrm{alg}[E]} K$ on $C_K$ agreeing with `D₂.classAct` (hypothesis `hact₂`), together with a group isomorphism $\iota : G/N \simeq (K \simeq_{\mathrm{alg}[E]} K)$ such that $\iota(gN)$ acts on each element of $K$ as $g$ does. The conclusion asserts that the type of isomorphisms, in the category of $\mathbb{Z}$-linear representations of $G/N$, between the representation on the $N$-invariants of $C_F$ and the restriction along $\iota$ of the representation of $K \simeq_{\mathrm{alg}[E]} K$ on $C_K$ is nonempty; only existence of such an isomorphism is claimed, no particular map being specified.
--
--   This is Galois descent for idele class groups: the $N$-invariants of $C_F$ are identified with $C_{F^N}$, compatibly with the identification $G/N \cong \mathrm{Gal}(F^N/E)$. It feeds the computations of the first and second cohomology of the idele class group used in the local–global arguments, being cited by [`NumberField.IdeleClassGroup.isZero_H1_of_isPGroup`](thm.html#NumberField.IdeleClassGroup.isZero_H1_of_isPGroup), [`NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup`](thm.html#NumberField.IdeleClassGroup.finite_H2_and_natCard_H2_le_card_of_isPGroup) and [`NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_isCyclic`](thm.html#NumberField.IdeleClassGroup.isZero_H1_and_natCard_H2_eq_card_of_isCyclic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_fixedField.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_fixedField
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (N : Subgroup (F ≃ₐ[E] F)) [N.Normal]
    (D₂ : IdeleGaloisDescent (𝓞 (IntermediateField.fixedField N)) E (IntermediateField.fixedField N))
    [MulDistribMulAction ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))
      (IdeleClassGroup (𝓞 (IntermediateField.fixedField N)) (IntermediateField.fixedField N))]
    (hact₂ : ∀ (g : (IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))
      (c : IdeleClassGroup (𝓞 (IntermediateField.fixedField N)) (IntermediateField.fixedField N)),
      g • c = D₂.classAct g c)
    (ι : (F ≃ₐ[E] F) ⧸ N ≃* ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N)))
    (hι : ∀ (g : F ≃ₐ[E] F) (x : IntermediateField.fixedField N),
      ((ι (QuotientGroup.mk g)) x : F) = g (x : F)) :
    Nonempty
      ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)).quotientToInvariants N ≅
        Rep.res ι.toMonoidHom
          (Rep.ofMulDistribMulAction
            ((IntermediateField.fixedField N) ≃ₐ[E] (IntermediateField.fixedField N))
            (IdeleClassGroup (𝓞 (IntermediateField.fixedField N)) (IntermediateField.fixedField N)))) := by sorry
