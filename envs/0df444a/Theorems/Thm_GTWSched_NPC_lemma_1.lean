-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_1
-- name    : GTWSched.NPC.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:47:50.291781+00:00
-- url     : https://prove2.me/theorems/59f8eac7-c0e8-43c7-9fdd-f7faf1a5efd3
-- title:
--   LEMMA 1, p. 333 — even-odd partition is NP-complete (given that Partition is)
-- statement:
--   **LEMMA 1.** The even-odd partition problem is NP-complete.
--
--   Precisely: if the language of Partition is NP-complete, then the language of even-odd partition (codes of positive, strictly increasing integers $x_1<\dots<x_{2n}$ admitting an equal-sum partition with exactly one of $x_{2i-1},x_{2i}$ in each part) is NP-complete:
--   $$\text{Partition NP-complete}\ \Longrightarrow\ \text{Even-odd partition NP-complete}.$$
--
--   The NP-completeness of Partition is the one fact the paper takes from Garey and Johnson (1979); even-odd partition is the source problem of the reduction proving THEOREM 1.
--
--   **Formalization Note** NP-completeness is the published `CookPvsNP.NPComplete`. `positivePartitionLang` restricts the imported binary encoding and equal-sum predicate to nonempty lists of positive integers, as stated on p. 333.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 333, LEMMA 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- LEMMA 1, p. 333, relative to the NP-completeness of PARTITION: the even-odd partition problem
is NP-complete. -/
theorem lemma_1 (hP : NPComplete positivePartitionLang) : NPComplete evenOddLang := by sorry

end GTWSched.NPC
