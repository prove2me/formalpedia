-- Prove2me | Theorems.Thm_OrderHom_gfp_mem_Icc_of_certificate
-- name    : OrderHom.gfp_mem_Icc_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:53:38.919802+00:00
-- url     : https://prove2.me/theorems/a5553cdd-4a38-489d-922e-4418f4aa6215
-- title:
--   Order Hom: gfp mem Icc of certificate
-- statement:
--   **The payoff, `gfp` side, dual.** A post-fixed-point lower candidate `lo` (`lo ≤ f lo`) together
--       with an upper bound `hi` over every post-fixed point sandwiches `f.gfp` between them --
--       `OrderHom.le_gfp`/`OrderHom.gfp_le`, the exact mirror of the `lfp` case above with the roles of
--       `lo`/`hi` swapped to match which side gets the easier one-directional hypothesis.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L69-L72
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L69-L72

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate
set_option autoImplicit true

theorem OrderHom.gfp_mem_Icc_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hpost : lo ≤ f lo) (hub : ∀ b, b ≤ f b → b ≤ hi) :
    lo ≤ f.gfp ∧ f.gfp ≤ hi := by sorry
