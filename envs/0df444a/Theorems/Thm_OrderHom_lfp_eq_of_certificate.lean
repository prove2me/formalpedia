-- Prove2me | Theorems.Thm_OrderHom_lfp_eq_of_certificate
-- name    : OrderHom.lfp_eq_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:51:44.70862+00:00
-- url     : https://prove2.me/theorems/6299a4bc-ff8f-4426-af0f-1640cbf946f7
-- title:
--   Order Hom: lfp eq of certificate
-- statement:
--   **The payoff, fully generalised.** A candidate `v` in any `CompleteLattice` that is an exact
--       fixed point of a monotone self-map `f`, and that lower-bounds every pre-fixed point of `f`,
--       *is* `f`'s least fixed point -- Knaster-Tarski's two pinning lemmas assembled via
--       `le_antisymm`, with no reference to `CSG`s, `reachOp`, or `[0, 1]`-valued functions anywhere in
--       the statement or proof. Checked against the cached Mathlib source
--       (`Mathlib/Order/FixedPoints.lean`) for a naming collision before adding this: none found.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachCertificate.lean#L39-L41
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/ReachCertificate.lean#L39-L41

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_ReachCertificate
set_option autoImplicit true

theorem OrderHom.lfp_eq_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hlb : ∀ b, f b ≤ b → v ≤ b) : f.lfp = v := by sorry
