-- Prove2me | Theorems.Thm_Lift_olift_evaluate
-- name    : Lift.olift_evaluate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T07:01:02.536501+00:00
-- url     : https://prove2.me/theorems/c186c124-92cd-4aa0-811e-ea52cbba412f
-- title:
--   Lift: olift evaluate
-- statement:
--   The Lift construction uses the olift evaluate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean#L169-L172
-- source:
--   https://github.com/eshelyaron/lean4-bdd/blob/89a95e2b6ff2873d8f4bfd704909fe58f5b0472b/Bdd/Lift.lean#L169-L172

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Lift
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


set_option autoImplicit true
attribute [local implicit_reducible] OBdd Bdd.Ordered
open Lift
attribute [local implicit_reducible] olift

theorem Lift.olift_evaluate {h : n ≤ n'} {O : OBdd n m} {I : Vector Bool n'} :
    (olift h O).evaluate I = O.evaluate (Vector.cast (by simpa) (I.take n)) := by sorry
