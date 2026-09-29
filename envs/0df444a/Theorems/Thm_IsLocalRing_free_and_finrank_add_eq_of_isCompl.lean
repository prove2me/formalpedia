-- Prove2me | Theorems.Thm_IsLocalRing_free_and_finrank_add_eq_of_isCompl
-- name    : IsLocalRing.free_and_finrank_add_eq_of_isCompl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/9f21ee3a-4366-54ae-a9e1-2ceab3691749
-- title:
--   Complementary summands of a finite free module over a local ring
-- statement:
--   Let $C$ be a commutative local ring and let $N$ be a $C$-module that is finitely generated and free (the module structure and the finiteness and freeness assumptions being typeclass hypotheses). Let $N_0$ and $N_1$ be submodules of $N$ that are complementary in the lattice of submodules, i.e. `IsCompl N0 N1`: their intersection is $0$ and their sum is all of $N$. The conclusion is a fivefold conjunction: $N_0$ is a free $C$-module; $N_0$ is a finitely generated $C$-module; $N_1$ is a free $C$-module; $N_1$ is a finitely generated $C$-module; and the ranks add, $$\operatorname{finrank}_C N_0 + \operatorname{finrank}_C N_1 = \operatorname{finrank}_C N,$$ where $\operatorname{finrank}$ is Mathlib's natural-number-valued rank. Note that the freeness and finiteness of the two complements are asserted as part of the same statement as the rank identity, so no separate hypothesis of freeness on $N_0$ or $N_1$ is needed.
--
--   This is the standard fact that a direct summand of a finitely generated free module over a local ring is again finitely generated and free, with additive rank; over a local ring finitely generated flat (equivalently projective) modules are free. It is used in the construction of bases adapted to a decomposition, being cited by [`GaloisLattice.exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing`](thm.html#GaloisLattice.exists_adaptedBasis_cornerSubmodule_of_involution_of_similitudePairing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_free_and_finrank_add_eq_of_isCompl.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.free_and_finrank_add_eq_of_isCompl
    {C : Type} [CommRing C] [IsLocalRing C] {N : Type} [AddCommGroup N] [Module C N]
    [Module.Finite C N] [Module.Free C N] (N0 N1 : Submodule C N) (h : IsCompl N0 N1) :
    Module.Free C N0 ∧ Module.Finite C N0 ∧ Module.Free C N1 ∧ Module.Finite C N1 ∧
      Module.finrank C N0 + Module.finrank C N1 = Module.finrank C N := by sorry
