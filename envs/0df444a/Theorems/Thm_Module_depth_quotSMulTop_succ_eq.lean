-- Prove2me | Theorems.Thm_Module_depth_quotSMulTop_succ_eq
-- name    : Module.depth_quotSMulTop_succ_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/68806686-85fe-553a-8659-03f745a7fc4f
-- title:
--   Depth drops by one modulo an M-regular element of 𝔪
-- statement:
--   Let $R$ be a commutative Noetherian local ring with maximal ideal $\mathfrak m =$ `maximalIdeal R`, and let $M$ be a finitely generated $R$-module. Let $x \in \mathfrak m$ be an element that acts regularly on $M$, i.e. multiplication by $x$ is injective on $M$ (`IsSMulRegular M x`). Then the depth of the quotient $M/xM$ (`QuotSMulTop x M`) plus one equals the depth of $M$, the equality being one of elements of $\mathbb N \cup \{\infty\}$. Here, for an $R$-module $N$, [`Module.depth R N`](def/Patching_SystemTypes.html#L34) is defined as the supremum in $\mathbb N\infty$ of the lengths of those finite lists $s$ of elements of $R$ all of whose entries lie in $\mathfrak m$ and which form a weakly $N$-regular sequence in the sense of Mathlib's `Sequence.IsWeaklyRegular`; in particular the empty list always qualifies, so the supremum is over a nonempty set.
--
--   This is the standard statement that depth drops by exactly one when one divides out an $M$-regular element of the maximal ideal, the inductive engine behind arguments on depth such as the Auslander–Buchsbaum equality and the freeness of finite modules of maximal depth over a regular local ring. Within the project it is used in the Cohen–Macaulay bookkeeping ([`IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height`](thm.html#IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height)) and in establishing unique factorisation for regular local rings ([`IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing`](thm.html#IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_depth_quotSMulTop_succ_eq.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing RingTheory

theorem Module.depth_quotSMulTop_succ_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth R (QuotSMulTop x M) + 1 = Module.depth R M := by sorry
