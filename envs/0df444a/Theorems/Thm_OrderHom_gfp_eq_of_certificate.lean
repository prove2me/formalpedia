-- Prove2me | Theorems.Thm_OrderHom_gfp_eq_of_certificate
-- name    : OrderHom.gfp_eq_of_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:15.185536+00:00
-- url     : https://prove2.me/theorems/8a57ecb1-75a5-46b3-a811-ec3f8022f5e5
-- title:
--   Order Hom: gfp eq of certificate
-- statement:
--   **The payoff, fully generalised, dual to `OrderHom.lfp_eq_of_certificate`.** A candidate `v` in
--       any `CompleteLattice` that is an exact fixed point of a monotone self-map `f`, and that
--       upper-bounds every post-fixed point of `f` (`b ≤ f b`), *is* `f`'s greatest fixed point --
--       Knaster-Tarski's other two pinning lemmas, `le_gfp`/`gfp_le`, assembled via `le_antisymm`, with
--       no reference to `CSG`s, `safetyOp`, or `[0, 1]`-valued functions anywhere in the statement or
--       proof, exactly as the `lfp` version has none either.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SafetyCertificate.lean#L34-L36
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/SafetyCertificate.lean#L34-L36

import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_SafetyCertificate
set_option autoImplicit true

theorem OrderHom.gfp_eq_of_certificate {α : Type*} [CompleteLattice α] (f : α →o α) (v : α)
    (hfixed : f v = v) (hub : ∀ b, b ≤ f b → b ≤ v) : f.gfp = v := by sorry
