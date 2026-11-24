-- Prove2me | Theorems.Thm_LexPat_decodeUtf8One_ascii_roundtrip
-- name    : LexPat.decodeUtf8One_ascii_roundtrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:44.843111+00:00
-- url     : https://prove2.me/theorems/586fa1a9-3b9b-49a6-85d0-d0538f43407d
-- title:
--   Lex Pat: decode Utf8 One ascii roundtrip
-- statement:
--   An ASCII scalar encodes to one UTF-8 byte and decodes back to the same
--   scalar: a non-vacuous round trip on the real encoder and decoder.
--
--   Source: https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L48-L58
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L48-L58

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs
set_option autoImplicit true
open LexPat
open LexPat

theorem LexPat.decodeUtf8One_ascii_roundtrip (s : Scalar) (h : s.n < 0x80) :
    decodeUtf8One (encodeAscii s) 0 = .ok (s, 1) := by sorry
