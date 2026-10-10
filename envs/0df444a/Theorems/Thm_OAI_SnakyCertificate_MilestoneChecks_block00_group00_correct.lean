-- Prove2me | Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_group00_correct
-- name    : OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T13:10:12.165046+00:00
-- url     : https://prove2.me/theorems/61f59ab3-63f1-4c0b-a14b-693a8adeefd4
-- title:
--   35-move certificate: exact rows 0–7
-- statement:
--   The original certificate rows 0 through 7 have their exact required sets, envelopes and heights and the specified subset/origin/height invariants. Nonbase entries have correct indices, nonempty term lists and backward references.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean

import Definitions.Def_Snaky35Cache00
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate

theorem OAI.SnakyCertificate.MilestoneChecks.block00_group00_correct : (rowAt 0 = data_0 ∧ Good (rowAt 0) ∧ True) ∧ (rowAt 1 = data_1 ∧ Good (rowAt 1) ∧ True) ∧ (rowAt 2 = data_2 ∧ Good (rowAt 2) ∧ True) ∧ (rowAt 3 = data_3 ∧ Good (rowAt 3) ∧ True) ∧ (rowAt 4 = data_4 ∧ Good (rowAt 4) ∧ True) ∧ (rowAt 5 = data_5 ∧ Good (rowAt 5) ∧ True) ∧ (rowAt 6 = data_6 ∧ Good (rowAt 6) ∧ EntryGood 6) ∧ (rowAt 7 = data_7 ∧ Good (rowAt 7) ∧ EntryGood 7) ∧ True := by sorry
