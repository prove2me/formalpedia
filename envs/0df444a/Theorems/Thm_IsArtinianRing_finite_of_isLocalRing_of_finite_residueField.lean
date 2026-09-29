-- Prove2me | Theorems.Thm_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField
-- name    : IsArtinianRing.finite_of_isLocalRing_of_finite_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/b43d5c3e-0dd2-5fd9-9e1c-d9ef6c3c03c0
-- title:
--   An Artinian local ring with finite residue field is finite
-- statement:
--   Let $C$ be a commutative ring in the lowest universe which is local (so it has a unique maximal ideal $\mathfrak m =$ `maximalIdeal C`) and Artinian, and suppose the residue field $\mathrm{ResidueField}\,C = C/\mathfrak m$ has finitely many elements. The conclusion is that $C$ itself is a finite type, i.e. $C$ has only finitely many elements. The hypotheses are exactly the three ring-theoretic typeclass assumptions (commutative ring, local, Artinian) together with finiteness of the residue field; no separate Noetherian hypothesis is imposed, that being a consequence of Artinianness, and no assumption of characteristic or of the residue characteristic is made.
--
--   This is the standard fact that an Artin local ring is finite as soon as its residue field is, the ring having finite length with all simple subquotients isomorphic to $C/\mathfrak m$. It is used in the study of the residue fields of maximal ideals of $C \otimes_{\mathbb Z} \mathcal O$, namely by [`IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField`](thm.html#IsArtinianRing.isAlgClosed_residueField_of_isMaximal_tensorProduct_int_of_isAlgClosed_residueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsArtinianRing_finite_of_isLocalRing_of_finite_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsArtinianRing.finite_of_isLocalRing_of_finite_residueField
    (C : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Finite (ResidueField C)] : Finite C := by sorry
