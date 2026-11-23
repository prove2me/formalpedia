-- Prove2me | Theorems.Thm_Nary_ne_implies_dependency_getElem_ne
-- name    : Nary.ne_implies_dependency_getElem_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:35.932955+00:00
-- url     : https://prove2.me/theorems/83ac0a22-97a1-4ee4-b070-07a50d7613ab
-- title:
--   Nary: ne implies dependency get Elem ne
-- statement:
--   The Nary construction uses the ne implies dependency get Elem ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L76-L80
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L76-L80

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
set_option autoImplicit true
open Nary

theorem Nary.ne_implies_dependency_getElem_ne {f : Func n α β} {I J : Vector α n} :
    f I ≠ f J → ∃ i : Nary.Dependency f, I[i.1] ≠ J[i.1] := by sorry
