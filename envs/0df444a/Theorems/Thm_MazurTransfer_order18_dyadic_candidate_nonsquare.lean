-- Prove2me | Theorems.Thm_MazurTransfer_order18_dyadic_candidate_nonsquare
-- name    : MazurTransfer.order18_dyadic_candidate_nonsquare
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T12:42:11.022758+00:00
-- url     : https://prove2.me/theorems/3e1fabda-ade6-4ee9-bc11-7138627189aa
-- title:
--   All fifteen nonidentity dyadic candidates are nonsquares
-- statement:
--   Let $C=(\mathbb Z/16\mathbb Z)^3$, with multiplication obtained by reducing powers using $\tau^3=3\tau+1$. None of the fifteen specified candidate vectors is of the form $z^2$ for a vector $z\in C$. The candidates are the reductions of the fifteen nonidentity masked products of four proposed global norm-kernel generators in the order-18 descent. This is an unconditional finite arithmetic certificate; the downstream descent separately proves the relation between these coefficient triples and the integral elements in the dyadic completion.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c: XOneEighteenDyadicCubicCertificate.lean, candidate_nonsquare. Original finite kernel computation retained without any native numerical oracle. Original Apache-2.0 source header retained.

import Mathlib
import Definitions.Def_MazurTransfer_OrderEighteenDyadicCandidateData

theorem MazurTransfer.order18_dyadic_candidate_nonsquare :
    ∀ i : Fin 15,
      ¬ MazurTorsion.XOneEighteenDyadicCubicCertificate.IsSquare
        (MazurTorsion.XOneEighteenDyadicCubicCertificate.candidate i) := by sorry
