-- Prove2me | Theorems.Thm_IsArtinianRing_finite_of_finite_residueField
-- name    : IsArtinianRing.finite_of_finite_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/502e56de-059f-5e41-9105-c35a9211505a
-- title:
--   Artinian local ring with finite residue field is finite
-- statement:
--   Let $R$ be a commutative ring that is Artinian as a ring (`IsArtinianRing`) and local (`IsLocalRing`, so that it has a unique maximal ideal $\mathfrak{m}_R$ and an associated residue field $R/\mathfrak{m}_R$), and suppose that the residue field `IsLocalRing.ResidueField R` is finite, in the sense of Mathlib's `Finite` typeclass (finiteness as a type, not merely a cardinality bound). The conclusion is that the type $R$ itself is finite. No separation, topology or base-ring structure enters: the hypotheses are purely the Artinian, local and finite-residue-field conditions, and the conclusion is the `Finite` instance for $R$.
--
--   This is the standard fact that an Artinian local ring with finite residue field is a finite ring, the finiteness step underlying the compactness of complete Noetherian local rings with finite residue field in deformation theory. It is used here to show that the quotients of a pro-Artinian ring by open ideals are finite, via [`IsProartinian.finite_quotient_of_isOpen`](thm.html#IsProartinian.finite_quotient_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsArtinianRing_finite_of_finite_residueField.lean

import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsArtinianRing.finite_of_finite_residueField (R : Type*) [CommRing R] [IsArtinianRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)] :
    Finite R := by sorry
