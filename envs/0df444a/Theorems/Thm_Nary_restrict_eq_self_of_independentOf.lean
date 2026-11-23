-- Prove2me | Theorems.Thm_Nary_restrict_eq_self_of_independentOf
-- name    : Nary.restrict_eq_self_of_independentOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:38:40.852051+00:00
-- url     : https://prove2.me/theorems/bcd42ad1-5d9f-4ea8-b7af-105b2a9c4d33
-- title:
--   Nary: restrict eq self of independent Of
-- statement:
--   The Nary construction uses the restrict eq self of independent Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L90-L95
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Nary.lean#L90-L95

import Mathlib.Data.Vector.Basic
import Definitions.Def_Bdd_Nary
set_option autoImplicit true
open Nary

theorem Nary.restrict_eq_self_of_independentOf : IndependentOf f i → (restrict f c i) = f := by sorry
