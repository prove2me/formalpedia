-- Prove2me | Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
-- name    : OAI.SnakyCertificate.MilestoneChecks.chunk_lookups
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T12:50:31.424155+00:00
-- url     : https://prove2.me/theorems/7a40f4c9-f307-4029-b539-67f16b6ecd2a
-- title:
--   35-move certificate: exact lookup in all 31 table chunks
-- statement:
--   Each of the 31 printed table chunks occupies its exact consecutive position in the original 610-entry certificate array, uniformly over the indices within that chunk.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean

import Definitions.Def_Snaky35Core
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate

theorem OAI.SnakyCertificate.MilestoneChecks.chunk_lookups : (∀ j : ℕ, j < 20 → entryAt (6 + j) = tableChunk_0[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (26 + j) = tableChunk_1[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (46 + j) = tableChunk_2[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (66 + j) = tableChunk_3[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (86 + j) = tableChunk_4[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (106 + j) = tableChunk_5[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (126 + j) = tableChunk_6[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (146 + j) = tableChunk_7[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (166 + j) = tableChunk_8[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (186 + j) = tableChunk_9[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (206 + j) = tableChunk_10[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (226 + j) = tableChunk_11[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (286 + j) = tableChunk_14[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (306 + j) = tableChunk_15[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (346 + j) = tableChunk_17[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (366 + j) = tableChunk_18[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (386 + j) = tableChunk_19[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (406 + j) = tableChunk_20[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (426 + j) = tableChunk_21[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (466 + j) = tableChunk_23[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (506 + j) = tableChunk_25[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (526 + j) = tableChunk_26[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (546 + j) = tableChunk_27[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (566 + j) = tableChunk_28[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 20 → entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry) ∧ (∀ j : ℕ, j < 10 → entryAt (606 + j) = tableChunk_30[j]?.getD emptyEntry) ∧ True := by sorry
