-- Prove2me | Theorems.Thm_GTWSched_NPC_evenOdd_polyReducible_td
-- name    : GTWSched.NPC.evenOdd_polyReducible_td
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-27T06:40:07.570244+00:00
-- url     : https://prove2.me/theorems/80c6abd2-84a0-4f8b-a7ab-a31774395831
-- title:
--   Polynomial-Time Reduction from Even-Odd Partition to Total Discrepancy
-- statement:
--   The Even-Odd Partition language ($\text{evenOddLang}$) is polynomial-time many-one reducible to the Total Discrepancy scheduling language ($\text{tdLang}$) via the $(2n+2)$-task instance $D$ of Theorem 1 (Garey, Tarjan & Wilfong 1988, pp. 336–337).
-- source:
--   Garey, Tarjan & Wilfong (1988), One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Operations Research 36(2), Theorem 1, pp. 336–337

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

theorem evenOdd_polyReducible_td :
    PolyReducible evenOddLang tdLang := by sorry

end GTWSched.NPC
