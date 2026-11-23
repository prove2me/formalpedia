-- Prove2me | Theorems.Thm_Nary_restrict_independentOf
-- name    : Nary.restrict_independentOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:41.973871+00:00
-- url     : https://prove2.me/theorems/64cb849d-2a9a-42d7-a397-933a770ed7bc
-- title:
--   Nary: restrict independent Of
-- statement:
--   The Nary construction uses the restrict independent Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L88-L88
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L88-L88

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
set_option autoImplicit true
open Nary

theorem Nary.restrict_independentOf : IndependentOf (restrict f c i) i := by sorry
