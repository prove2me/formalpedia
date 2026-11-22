-- Prove2me | Theorems.Thm_OrderHom_lfp_mem_Icc_of_certificate
-- name    : OrderHom.lfp_mem_Icc_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:53:32.334208+00:00
-- url     : https://prove2.me/theorems/f4e6d92a-1485-4c7a-a980-5eb287a1ab3e
-- title:
--   Order Hom: lfp mem Icc of certificate
-- statement:
--   **The payoff, `lfp` side.** A lower bound `lo` over every pre-fixed point, together with an
--       upper candidate `hi` that is itself a pre-fixed point (`f hi ≤ hi`, not the exact-certificate's
--       stronger `f hi = hi`), sandwiches `f.lfp` between them. `OrderHom.le_lfp`/`OrderHom.lfp_le`
--       assembled directly, no `le_antisymm` needed since the two conclusions are independent
--       inequalities rather than two sides of one equality.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L60-L63
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntervalCertificate.lean#L60-L63

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate
set_option autoImplicit true

theorem OrderHom.lfp_mem_Icc_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α)
    (lo hi : α) (hlb : ∀ b, f b ≤ b → lo ≤ b) (hpre : f hi ≤ hi) :
    lo ≤ f.lfp ∧ f.lfp ≤ hi := by sorry
