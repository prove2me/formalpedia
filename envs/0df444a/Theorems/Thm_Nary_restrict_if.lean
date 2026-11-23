-- Prove2me | Theorems.Thm_Nary_restrict_if
-- name    : Nary.restrict_if
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:40.057865+00:00
-- url     : https://prove2.me/theorems/0724ccab-7c10-49eb-8637-488c891ca89f
-- title:
--   Nary: restrict if
-- statement:
--   The Nary construction uses the restrict if property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L97-L100
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L97-L100

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
set_option autoImplicit true
open Nary

theorem Nary.restrict_if {c : Func n α Bool} :
    restrict (fun I ↦ if c I then f I else g I) b i =
    fun I ↦ if (restrict c b i I) then (restrict f b i I) else (restrict g b i I) := by sorry
