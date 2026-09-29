-- Prove2me | Theorems.Thm_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one
-- name    : NumberField.InfPlaceDecomp.extensionEmbedding_smul_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8d29d7f2-d5c6-5b2b-87ad-cdd483e9c29c
-- title:
--   Nontrivial elements of D_w act as complex conjugation
-- statement:
--   Let $E$ and $K$ be fields with $K$ an $E$-algebra, and let $w$ be an infinite place of $K$, that is, an element of `InfinitePlace K`. Write `decomp E K w` for the stabiliser of $w$ in the group $K \simeq_{\mathrm{alg}[E]} K$ of $E$-algebra automorphisms of $K$ acting on infinite places, a subgroup of that automorphism group; the project equips the completion `w.Completion` of $K$ at $w$ with an action of this stabiliser. Let $\sigma$ be an element of `decomp E K w` with $\sigma \neq 1$, and let $x$ be any element of `w.Completion`. The assertion is that Mathlib's embedding $\iota_w =$ `InfinitePlace.Completion.extensionEmbedding w` of the completion into $\mathbb{C}$ satisfies $\iota_w(\sigma \cdot x) = \overline{\iota_w(x)}$, the bar being `starRingEnd ℂ`, i.e. complex conjugation. No number-field or finiteness hypothesis on $E$ or $K$ is imposed; in particular the statement is vacuous when the stabiliser is trivial.
--
--   This identifies the action of a nontrivial element of the decomposition group of an archimedean place on the completion $K_w$ with complex conjugation under the canonical embedding $K_w \hookrightarrow \mathbb{C}$; in particular such a place is complex and $\iota_w$ is conjugate-equivariant. It is the transport lemma used in the computation of the local archimedean Tate cohomology groups, cited by [`NumberField.InfPlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1`](thm.html#NumberField.InfPlaceDecomp.card_tateH0_units_eq_card_and_subsingleton_tateHneg1).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfPlaceDecomp_extensionEmbedding_smul_of_ne_one.lean

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open NumberField
open scoped NumberField.InfPlaceDecomp

theorem NumberField.InfPlaceDecomp.extensionEmbedding_smul_of_ne_one (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (hσ : σ ≠ 1) (x : w.Completion) :
    InfinitePlace.Completion.extensionEmbedding w (σ • x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w x) := by sorry
