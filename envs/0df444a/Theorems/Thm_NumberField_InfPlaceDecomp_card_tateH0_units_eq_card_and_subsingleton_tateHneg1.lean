-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1
-- name    : NumberField.InfPlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0ba6ee71-f98d-5903-bc08-d314f22763b6
-- title:
--   Tate cohomology of the units at an infinite place
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra, and let $w$ be an infinite place of $K$. Write $D =$ `decomp E K w` for the stabiliser of $w$ in the group $K \simeq_{\text{alg}[E]} K$ of $E$-algebra automorphisms of $K$, assumed finite, and let it act on the unit group $(K_w)^\times$ of the completion $K_w$ of $K$ at $w$ through the induced action on $K_w$; this multiplicative action is regarded as the $\mathbb{Z}$-linear representation `Rep.ofMulDistribMulAction D (w.Completion)ˣ` on the additive group $\mathrm{Additive}\,(K_w)^\times$. For such a representation $\rho$, `tateH0` is the quotient of the invariants by the image of the map $\rho.\mathrm{normBar}$ from the coinvariants to the invariants induced by the norm $x \mapsto \sum_{h \in D} h\cdot x$, and `tateHneg1` is the kernel of that same map. The assertion is twofold: first, the cardinality of $\hat H^0(D, (K_w)^\times)$, in the sense of `Nat.card`, equals the cardinality of $D$; second, $\hat H^{-1}(D, (K_w)^\times)$ is a subsingleton, i.e. the trivial group.
--
--   This is the computation of the Tate cohomology of the local units at an archimedean place: the norm index equals the order of the decomposition group (which is $1$ or $2$), and Hilbert's theorem 90 for $\mathbb{C}/\mathbb{R}$ gives the vanishing in degree $-1$. It feeds the corresponding statement for the archimedean part of the idele class module, [`NumberField.ArchIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1`](thm.html#NumberField.ArchIdele.card_tateH0_obj_eq_prod_and_subsingleton_tateHneg1), where the product over the infinite places is taken.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_card_tateH0_units_eq_card_and_subsingleton_tateHneg1.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1 (E K : Type) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) [Fintype (NumberField.InfPlaceDecomp.decomp E K w)] :
    Nat.card (Rep.ofMulDistribMulAction (NumberField.InfPlaceDecomp.decomp E K w) (w.Completion)ˣ).tateH0 =
      Nat.card (NumberField.InfPlaceDecomp.decomp E K w) ∧
    Subsingleton (Rep.ofMulDistribMulAction (NumberField.InfPlaceDecomp.decomp E K w) (w.Completion)ˣ).tateHneg1 := by sorry
