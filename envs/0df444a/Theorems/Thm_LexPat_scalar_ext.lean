-- Prove2me | Theorems.Thm_LexPat_scalar_ext
-- name    : LexPat.scalar_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:34:43.084482+00:00
-- url     : https://prove2.me/theorems/03a35a9e-c0e7-4648-82bf-06b307027d9d
-- title:
--   Lex Pat: scalar ext
-- statement:
--   A scalar is determined by its value; the validity proofs are irrelevant.
--
--   Source: https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L21-L25
-- source:
--   https://github.com/scidonia/lexpat/blob/15eee92b433940e5481f09c7f77e6f833e5f684d/LexPat/Encoding/Proofs.lean#L21-L25

import Definitions.Def_LexPat_Encoding
import Definitions.Def_LexPat_Encoding_Proofs
set_option autoImplicit true
open LexPat
open LexPat

theorem LexPat.scalar_ext {t s : Scalar} (h : t.n = s.n) : t = s := by sorry
