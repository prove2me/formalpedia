-- Prove2me | Theorems.Thm_GTWSched_NPC_theorem_1
-- name    : GTWSched.NPC.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:52:06.139023+00:00
-- url     : https://prove2.me/theorems/4aa7a112-9e3a-475e-9983-4047c81b9d2b
-- title:
--   THEOREM 1, p. 336 — the total discrepancy problem is NP-complete (given that Partition is)
-- statement:
--   **THEOREM 1.** The total discrepancy problem is NP-complete.
--
--   The total discrepancy problem asks, for $N$ tasks with lengths $l_i\in\mathbb Z^+$, preferred midtimes $M_i\in\mathbb Z^+$ and a threshold $k\in\mathbb Z^+$, whether some one-processor schedule $S$ (nonnegative real starting times $s_i$, nonoverlapping execution intervals $[s_i,s_i+l_i]$) has
--   $$\mathrm{cost}(S)=\sum_{i=1}^N|m_i(S)-M_i|\le k,\qquad m_i(S)=s_i+l_i/2 .$$
--   The statement is: if Partition is NP-complete, then this problem (as the language of codes of its yes-instances) is NP-complete.
--
--   Since preferred midtimes and preferred starting times are equivalent ($a_i=M_i-l_i/2$), it follows that minimizing the total discrepancy from preferred starting times on one processor is NP-hard.
--
--   **Formalization Note** NP-completeness is the published `CookPvsNP.NPComplete`; `positivePartitionLang` uses nonempty lists of positive integers, matching the paper's source problem. The NP-completeness of Partition (Garey and Johnson 1979) is the only fact the paper imports and is the hypothesis. The paper's construction D has half-integer midtimes and threshold, so a reduction to the integer-valued language must rescale. Nonnegative starting times are a standing assumption of the model (p. 336–337) and are essential to the reduction.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336, THEOREM 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- THEOREM 1, p. 336, relative to the NP-completeness of PARTITION: the total discrepancy problem
is NP-complete. -/
theorem theorem_1 (hP : NPComplete positivePartitionLang) : NPComplete tdLang := by sorry

end GTWSched.NPC
