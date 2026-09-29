-- Prove2me | Theorems.Thm_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
-- name    : Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/5fed7a9b-6a9d-5eb6-8714-90865fae9409
-- title:
--   Finite modules of depth dim R over regular local rings are free
-- statement:
--   Let $R$ be a commutative ring that is a regular local ring, and let $M$ be an $R$-module (an additive commutative group with an $R$-module structure) that is finite over $R$, i.e. finitely generated. Here [`Module.depth R M`](def/Patching_SystemTypes.html#L34) is the supremum, taken in $\mathbb{N}\cup\{\infty\}$, of the lengths of those finite lists $s$ of elements of $R$ that form a weakly regular sequence on $M$ and all of whose entries lie in the maximal ideal of $R$; in particular the value is $\top$ when arbitrarily long such sequences exist. The hypothesis is that this depth, viewed in $\mathrm{WithBot}\ \mathbb{N}\cup\{\infty\}$ so that it can be compared with the Krull dimension, equals `ringKrullDim R`, the Krull dimension of $R$ as an element of $\mathrm{WithBot}\ \mathbb{N}\cup\{\infty\}$ (this comparison in particular rules out the value $\bot$). The conclusion is that $M$ is a free $R$-module.
--
--   This is the Auslander–Buchsbaum freeness criterion in the form used in the Taylor–Wiles patching argument: over a regular local ring, maximal depth for a finitely generated module forces freeness. It is used here to deduce that regular local rings are unique factorisation domains and, in the form of a flatness criterion over a regular local base of equal dimension, to establish freeness of patched modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing RingTheory

theorem Module.free_of_depth_eq_ringKrullDim_of_isRegularLocalRing
    (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : (Module.depth R M : WithBot ℕ∞) = ringKrullDim R) : Module.Free R M := by sorry
