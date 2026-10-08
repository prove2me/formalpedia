-- Prove2me | Theorems.Thm_GTWSched_NPC_td_mem_NP
-- name    : GTWSched.NPC.td_mem_NP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:50:51.020523+00:00
-- url     : https://prove2.me/theorems/39e5935f-65f8-4218-88a8-5bb0a3259663
-- title:
--   §2.1, p. 336 — the total discrepancy problem is in NP
-- statement:
--   The total discrepancy problem belongs to NP: the language of codes of instances $N,k\in\mathbb Z^+$, $M_i,l_i\in\mathbb Z^+$ for which some one-processor schedule $S$ with real starting times has $\sum_{i=1}^N|m_i(S)-M_i|\le k$ is in
--   $$\mathrm{NP}.$$
--
--   The paper leaves this "as a simple exercise".
--
--   **Formalization Note** NP is the published `CookPvsNP.NP`; the language is `tdLang`. A certificate cannot simply be a list of real starting times; a polynomial-size certificate exists because for a fixed task order the optimal starting times solve a linear program with integer data.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336, §2.1, before THEOREM 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- p. 336: the total discrepancy problem is in NP. -/
theorem td_mem_NP : tdLang ∈ NP BSym := by sorry

end GTWSched.NPC
