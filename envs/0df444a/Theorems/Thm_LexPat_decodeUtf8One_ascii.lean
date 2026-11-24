-- Prove2me | Theorems.Thm_LexPat_decodeUtf8One_ascii
-- name    : LexPat.decodeUtf8One_ascii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:44.740987+00:00
-- url     : https://prove2.me/theorems/f0f523b2-a8dd-4cd4-b4e6-bed95804048c
-- title:
--   Lex Pat: decode Utf8 One ascii
-- statement:
--   A byte below `0x80` decodes as a single ASCII scalar.
--
--   Source: https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L38-L44
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L38-L44

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs
set_option autoImplicit true
open LexPat
open LexPat

theorem LexPat.decodeUtf8One_ascii (data : ByteArray) (b : UInt8) (hb : data[0]? = some b)
    (h : b.toNat < 0x80) :
    ∃ (t : Scalar) (next : Nat),
      decodeUtf8One data 0 = .ok (t, next) ∧ t.n = b.toNat ∧ next = 1 := by sorry
