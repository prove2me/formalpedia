-- Prove2me | Theorems.Thm_LexPat_decodeUtf8One_rejects_overlong_two_byte
-- name    : LexPat.decodeUtf8One_rejects_overlong_two_byte
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:42.43372+00:00
-- url     : https://prove2.me/theorems/cbd24be7-904a-46aa-8d51-bc6242c2573f
-- title:
--   Lex Pat: decode Utf8 One rejects overlong two byte
-- statement:
--   The two-byte overlong lead bytes `0xC0` and `0xC1` are rejected as
--   `overlong` for *every* possible following byte sequence: the check happens
--   before any continuation byte is consulted.
--
--   Source: https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L30-L35
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L30-L35

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs
set_option autoImplicit true
open LexPat
open LexPat

theorem LexPat.decodeUtf8One_rejects_overlong_two_byte (data : ByteArray) (i : Nat) (b : UInt8)
    (hb : data[i]? = some b) (hlead : b = 0xC0 ∨ b = 0xC1) :
    ∃ off, decodeUtf8One data i = .error { reason := .overlong, offset := off } := by sorry
