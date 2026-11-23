-- Prove2me | Theorems.Thm_Nary_eq_of_forall_dependency_getElem_eq
-- name    : Nary.eq_of_forall_dependency_getElem_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:41.061814+00:00
-- url     : https://prove2.me/theorems/5decc66a-16a7-47ba-89bc-25e60f983aad
-- title:
--   Nary: eq of forall dependency get Elem eq
-- statement:
--   The Nary construction uses the eq of forall dependency get Elem eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L18-L74
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L18-L74

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
set_option autoImplicit true
open Nary

theorem Nary.eq_of_forall_dependency_getElem_eq {f : Func n α β} {I J : Vector α n} :
    (∀ (x : Dependency f), I[x.1] = J[x.1]) → f I = f J := by sorry
