-- Prove2me | Theorems.Thm_GTWSched_NPC_evenOdd_mem_NP
-- name    : GTWSched.NPC.evenOdd_mem_NP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:46:30.951202+00:00
-- url     : https://prove2.me/theorems/1d142c89-7318-40e0-bf59-03fe28426273
-- title:
--   Proof of LEMMA 1, p. 333 — even-odd partition is in NP
-- statement:
--   The even-odd partition problem belongs to NP: the language of binary codes of even-odd partition yes-instances (positive, strictly increasing integers $x_1<\dots<x_{2n}$, $n\ge1$, admitting a partition $X_1,X_2$ of equal sums with exactly one of $x_{2i-1},x_{2i}$ in $X_1$ for every $i$) is in
--   $$\mathrm{NP}.$$
--
--   This is the membership half of LEMMA 1.
--
--   **Formalization Note** NP is the published `CookPvsNP.NP` (one-tape Turing machines, polynomial checking relation); the language is `evenOddLang` over the published alphabet `BSym`.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 333, proof of LEMMA 1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_GTWSched_NPC_Schedules
import Definitions.Def_GTWSched_NPC_Problems

namespace GTWSched.NPC

open CookPvsNP ProjSchedTW.Complexity

/-- Proof of LEMMA 1, p. 333: the even-odd partition problem is in NP. -/
theorem evenOdd_mem_NP : evenOddLang ∈ NP BSym := by sorry

end GTWSched.NPC
