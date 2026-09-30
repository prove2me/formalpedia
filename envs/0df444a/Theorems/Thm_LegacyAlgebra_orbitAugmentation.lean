-- Prove2me | Theorems.Thm_LegacyAlgebra_orbitAugmentation
-- name    : LegacyAlgebra.orbitAugmentation
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:38:05.175953+00:00
-- url     : https://prove2.me/theorems/85478003-b7db-44ef-be81-1c0fc5d7a8b4
-- title:
--   Orbit augmentation kernel and rank formula
-- statement:
--   Let a group G act on a finite set X over any field k. The subspace spanned by e_(g·x) − e_x is exactly the kernel of the map that sums coefficients separately on each G-orbit. Its dimension is |X| − |X/G|. No transitivity or characteristic assumption is imposed, and the acting group need not be finite.
-- source:
--   Unpublished research note metabelian_pure_fiber_no_go.md, §3 (Orbit-rank theorem); SHA-256 3ba5b183826a2e93741d33827b5a1d701c3df2f6d31beeb3857cc2141849e3c8.

import Mathlib
import Definitions.Def_legacyOrbitAugmentation

set_option autoImplicit false

theorem LegacyAlgebra.orbitAugmentation
    (k G X : Type*) [Field k] [Group G] [MulAction G X] [Fintype X] :
    legacyOrbitAugmentation k G X =
        LinearMap.ker (Finsupp.lmapDomain k k
          (Quotient.mk (MulAction.orbitRel G X))) ∧
      Module.finrank k (legacyOrbitAugmentation k G X) =
        Fintype.card X - Nat.card (MulAction.orbitRel.Quotient G X) := by
  sorry
