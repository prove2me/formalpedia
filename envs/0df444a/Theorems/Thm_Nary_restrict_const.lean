-- Prove2me | Theorems.Thm_Nary_restrict_const
-- name    : Nary.restrict_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:35.829805+00:00
-- url     : https://prove2.me/theorems/50205bd6-cf0f-4d2a-81b2-06869185f937
-- title:
--   Nary: restrict const
-- statement:
--   The Nary construction uses the restrict const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L86-L86
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L86-L86

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
set_option autoImplicit true
open Nary

theorem Nary.restrict_const : restrict (Function.const _ b) c i = (Function.const _ b) := by sorry
