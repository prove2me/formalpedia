-- Prove2me | Theorems.Thm_HGASUndecidable_Main_guardedPaddingMap_computable
-- name    : HGASUndecidable.Main.guardedPaddingMap_computable
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:47.410072+00:00
-- url     : https://prove2.me/theorems/3f39c3d5-c103-46cd-9247-82abab01ccc5
-- title:
--   Computability of guarded option decoding and padding composition
-- statement:
--   Given computable code validity, computable padding, and a computable lift $f$, the total guarded map `guardedPaddingMap` is computable. This is the finite computability composition principle for nested `Option.bind`, decidable format tests, canonical encoding/decoding, and a constant invalid fallback. The statement keeps validity and padding as independent inputs so it tests only the guarded composition.
-- source:
--   Paper #1477, Theorem 2.1 (printed pp. 11–12/PDF 13–14), where step (i) applies a computable lift and step (ii) pads; the explicitly guarded version ensures totality while excluding malformed and wrong-format data.

import Definitions.Def_HGASUndecidable_Main_PaddingCodes

theorem HGASUndecidable.Main.guardedPaddingMap_computable
    (n₀ k₀ n j : ℕ) [DecidablePred HGASUndecidable.Main.ValidCode]
    (hn : Nat.choose (n₀+k₀-1) k₀ ≤ n) (f : ℕ → ℕ)
    (hv : ComputablePred HGASUndecidable.Main.ValidCode)
    (hp : Computable (HGASUndecidable.Main.paddingCode hn j)) (hf : Computable f) :
    Computable (HGASUndecidable.Main.guardedPaddingMap n₀ k₀ n j hn f) := by sorry
