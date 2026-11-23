-- Prove2me | Theorems.Thm_HGASUndecidable_Main_manyOneHard_not_computablePred
-- name    : HGASUndecidable.Main.manyOneHard_not_computablePred
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:25.812978+00:00
-- url     : https://prove2.me/theorems/21625236-6119-4b31-be3d-7ca3f7c416b7
-- title:
--   Many-one hardness implies undecidability
-- statement:
--   Let $S\subseteq\mathbb N$ be a many-one hard set, meaning that every recursively enumerable subset of $\mathbb N$ many-one reduces to $S$. Then
--
--   $$
--   S\text{ is many-one hard}\quad\Longrightarrow\quad S\text{ is undecidable}.
--   $$
--
--   Equivalently, no total computable predicate decides membership in $S$. This is the standard computability transfer used to extract undecidability from the many-one completeness of the global-asymptotic-stability decision problems.
--
--   **Formalization Note.** Decidable predicates are represented by Mathlib's `ComputablePred`, while many-one hardness is the mission predicate `ManyOneHard` over `REPred` and `ManyOneReducible`.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §3.1, facts (C1) and (C3) and the paragraph immediately following (C3), printed p. 14 (PDF p. 16).

import Definitions.Def_HGASUndecidable_Main_Codes
import Mathlib.Computability.Halting

open Filter Topology MeasureTheory
open scoped BigOperators

theorem HGASUndecidable.Main.manyOneHard_not_computablePred (S : ℕ → Prop) :
    ManyOneHard S → ¬ ComputablePred S := by sorry
