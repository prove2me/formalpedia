-- Prove2me | Theorems.Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
-- name    : Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/26b99249-a0c6-5966-a290-2589b4fe5894
-- title:
--   Depth is bounded by dim R/𝔭 for associated primes
-- statement:
--   Let $R$ be a commutative ring that is local and Noetherian, and let $M$ be an $R$-module which is an additive commutative group with $R$-action and is finitely generated over $R$. Let $p$ be an ideal of $R$ that belongs to $\mathrm{associatedPrimes}\ R\ M$, i.e. $p$ is an associated prime of $M$: it is prime and arises as the annihilator of some element of $M$. The conclusion compares two invariants. On the left, [`Module.depth R M`](def/Patching_SystemTypes.html#L34) is the supremum, taken in $\mathbb{N}\cup\{\infty\}$, of the lengths of those finite lists $s$ of elements of $R$ which form a weakly regular sequence on $M$ and all of whose entries lie in the maximal ideal of $R$; this value is then coerced into $\mathbb{N}\cup\{\infty\}$ adjoined a bottom element. On the right is `ringKrullDim (R ⧸ p)`, the Krull dimension of the quotient ring $R/p$, taken with values in $\mathbb{N}\cup\{\infty\}$ together with a bottom element for the zero ring. The assertion is the inequality $\operatorname{depth}_R M \le \dim R/p$ in that ordered value type.
--
--   This is the standard bound $\operatorname{depth} M \le \dim R/\mathfrak p$ for every associated prime $\mathfrak p$ of a finitely generated module over a Noetherian local ring, a refinement of $\operatorname{depth} M \le \dim R$ which encodes the unmixedness of Cohen–Macaulay modules. It is used in the commutative-algebra layer supporting the patching argument, in particular by [`IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height`](thm.html#IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing RingTheory

theorem Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} (hp : p ∈ associatedPrimes R M) :
    (Module.depth R M : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by sorry
