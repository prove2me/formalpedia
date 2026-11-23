-- Prove2me | Theorems.Thm_Lift_olift_reduced
-- name    : Lift.olift_reduced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:02:15.929592+00:00
-- url     : https://prove2.me/theorems/c9da2eac-067f-4663-b2be-4ae72d422911
-- title:
--   Lift: olift reduced
-- statement:
--   The Lift construction uses the olift reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean#L194-L198
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean#L194-L198

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Lift
set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Lift
attribute [local implicit_reducible] olift

theorem Lift.olift_reduced {h : n ≤ n'} {O : OBdd n m} : O.Reduced → (olift h O).Reduced := by sorry
