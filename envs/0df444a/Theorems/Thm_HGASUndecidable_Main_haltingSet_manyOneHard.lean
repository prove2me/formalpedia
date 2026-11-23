-- Prove2me | Theorems.Thm_HGASUndecidable_Main_haltingSet_manyOneHard
-- name    : HGASUndecidable.Main.haltingSet_manyOneHard
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:40:01.570772+00:00
-- url     : https://prove2.me/theorems/c58bdffd-fae3-433e-9ab3-623b9a3bd750
-- title:
--   Many-one hardness of the universal halting set
-- statement:
--   The universal halting predicate $K$ is many-one hard for the recursively enumerable subsets of $\mathbb N$: for every recursively enumerable predicate $A$, there is a total computable function $r$ such that
--   $$
--   a\in A\quad\Longleftrightarrow\quad r(a)\in K.
--   $$
--   This supplies the computability-theoretic starting point for the reductions to stability decision problems. The proof uses a partial-recursive program for $A$ and the computable pairing map $a\mapsto\langle c,a\rangle$, where $c$ codes that program.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), Section 3.1, facts (C1) and (C3), printed pp. 13–14 (PDF 15–16)

import Definitions.Def_HGASUndecidable_Main_Codes

open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

theorem haltingSet_manyOneHard : ManyOneHard haltingSet := by sorry
