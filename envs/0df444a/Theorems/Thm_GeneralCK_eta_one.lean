-- Prove2me | Theorems.Thm_GeneralCK_eta_one
-- name    : GeneralCK.eta_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T20:56:42.846349+00:00
-- url     : https://prove2.me/theorems/604fbbf0-3648-4c35-a9aa-9b36986fe348
-- title:
--   The entropy profile vanishes at entropy one
-- statement:
--   For the entropy profile $\eta$ defined in the Bellman interface, $$\eta(1)=0.$$ The value is the designated endpoint branch in the definition of $\eta$, and it is used when evaluating the Bellman profile at maximal binary entropy.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ProfileBasics.lean#L34-L34

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement
import Definitions.Def_GeneralCK_bellman

open GeneralCK

@[simp] theorem GeneralCK.eta_one : eta 1 = 0 := by sorry
