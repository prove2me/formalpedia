-- Prove2me | Theorems.Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_of_isScalarTower
-- name    : NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_of_isScalarTower
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/f9d52de5-6269-5a2d-ac6e-a6d10c2aeec2
-- title:
--   Galois descent for idele classes at an intermediate field
-- statement:
--   Let $E$, $F$, $N$ be number fields with algebra maps $E \to F$, $E \to N$, $F \to N$ forming a scalar tower, and with $N/E$ Galois; write $G = N \simeq_{\text{alg}[E]} N$ and $\mathcal{O}_N$, $\mathcal{O}_F$ for the rings of integers. The idele class group $C_N$ is the quotient of $(\mathbb{A}_N)^\times$ (the units of `AdeleRing (𝓞 N) N`) by the image of $N^\times$ under `algebraMap`, and similarly $C_F$. Assume given: a descent datum $D$ for $N/E$, namely a monoid homomorphism from $G$ to the ring automorphisms of $\mathbb{A}_N$ which is compatible with `algebraMap` from $N$ and whose values are continuous, together with a `MulDistribMulAction` of $G$ on $C_N$ whose action agrees with the induced quotient action `D.classAct`; the analogous datum $D'$ for $F/E$ with an action of $\mathrm{Gal}(F/E)$ on $C_F$ agreeing with `D'.classAct`; a normal subgroup $S \le G$; and a group isomorphism $\iota : G/S \to \mathrm{Gal}(F/E)$ such that $\iota(gS)$ agrees with $g$ on the image of $F$ in $N$. The conclusion asserts that the type of isomorphisms, in the category of representations of $G/S$, between the $S$-invariants of the representation attached to $C_N$ and the restriction along $\iota$ of the representation attached to $C_F$, is nonempty; only existence of such an isomorphism is claimed, no specific map.
--
--   This is Galois descent for idele class groups, here in the form $C_N^{S} \cong C_F$ as $G/S$-modules for an arbitrary intermediate field $F$ presented through an isomorphism $\iota : G/S \cong \mathrm{Gal}(F/E)$ rather than as the fixed field of $S$; the identification of the invariants rests on Hilbert's Theorem 90 for $N^\times$ over $F$ and on the identification of the $S$-fixed ideles of $N$ with the ideles of $F$. It feeds the computations of the second cohomology of the idele class group used in the Herbrand-quotient arguments, in particular [`M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup`](thm.html#M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup) and its $p$-group variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleClassGroup_nonempty_quotientToInvariants_iso_of_isScalarTower.lean

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField M4aHerbrand CategoryTheory

theorem NumberField.IdeleClassGroup.nonempty_quotientToInvariants_iso_of_isScalarTower
    (E F N : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field N] [NumberField N]
    [Algebra E F] [Algebra E N] [Algebra F N] [IsScalarTower E F N] [IsGalois E N]
    (D : IdeleGaloisDescent (𝓞 N) E N)
    [MulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)]
    (hact : ∀ (g : N ≃ₐ[E] N) (c : IdeleClassGroup (𝓞 N) N), g • c = D.classAct g c)
    (D' : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact' : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D'.classAct g c)
    (S : Subgroup (N ≃ₐ[E] N)) [S.Normal]
    (ι : (N ≃ₐ[E] N) ⧸ S ≃* (F ≃ₐ[E] F))
    (hι : ∀ (g : N ≃ₐ[E] N) (x : F),
      algebraMap F N (ι (QuotientGroup.mk g) x) = g (algebraMap F N x)) :
    Nonempty
      ((Rep.ofMulDistribMulAction (N ≃ₐ[E] N) (IdeleClassGroup (𝓞 N) N)).quotientToInvariants S ≅
        Rep.res ι.toMonoidHom
          (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) := by sorry
