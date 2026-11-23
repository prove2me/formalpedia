-- Prove2me | Theorems.Thm_Lift_olift_olift
-- name    : Lift.olift_olift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:03.58028+00:00
-- url     : https://prove2.me/theorems/1d312856-c8be-4293-8cd6-f46bae48ba39
-- title:
--   Lift: olift olift
-- statement:
--   The Lift construction uses the olift olift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean#L201-L203
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean#L201-L203

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Lift
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Lift
attribute [local implicit_reducible] olift

theorem Lift.olift_olift {h1 : n ≤ n'} {h2 : n' ≤ n''} {O : OBdd n m} : olift h2 (olift h1 O) = olift (.trans h1 h2) O := by sorry
