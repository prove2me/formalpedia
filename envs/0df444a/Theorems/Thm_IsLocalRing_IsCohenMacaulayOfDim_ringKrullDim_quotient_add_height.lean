-- Prove2me | Theorems.Thm_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height
-- name    : IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/76c75753-c462-5d46-b8a2-8195ec77c0d3
-- title:
--   Dimension formula dim R/𝔭+ht𝔭=d in Cohen–Macaulay local rings
-- statement:
--   Let $R$ be a commutative ring which is local and Noetherian, and let $d$ be a natural number. Assume $R$ is Cohen–Macaulay of dimension $d$ in the sense of the predicate `IsCohenMacaulayOfDim`, i.e. that the Krull dimension `ringKrullDim R` equals $d$ and that [`Module.depth R R`](def/Patching_SystemTypes.html#L34) equals $d$, where the depth of a module is the supremum, in $\mathbb N\cup\{\infty\}$, of the lengths of those finite lists $s$ of elements of $R$ which form a weakly regular sequence on the module and all of whose entries lie in the maximal ideal of $R$. Let $\mathfrak p$ be a prime ideal of $R$. Then $$\operatorname{ringKrullDim}(R/\mathfrak p)+\operatorname{height}(\mathfrak p)=d,$$ the equation being one of extended values (the Krull dimension takes values in $\mathbb N\cup\{\infty\}$ together with a bottom element, the height in $\mathbb N\cup\{\infty\}$, and $d$ is regarded as such a value). In particular both summands are finite and the dimension of $R/\mathfrak p$ is $d-\operatorname{height}(\mathfrak p)$.
--
--   This is the classical dimension formula for Cohen–Macaulay local rings, which also expresses that such a ring is equidimensional and has no embedded primes. It is used in the construction of the relative group law on Jacobians of curves with good reduction, where dimension counts on local rings of the base control the extension of rational maps across the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.lean

import Mathlib
import Definitions.Def_Patching_CohenMacaulayOfDim

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}
    (h : IsCohenMacaulayOfDim R d) (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) + p.height = d := by sorry
