-- Prove2me | Theorems.Thm_J6Seg_ChB_chunk_budget_at
-- name    : J6Seg.ChB.chunk_budget_at
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:54:01.17624+00:00
-- url     : https://prove2.me/theorems/f4b21ed5-f462-45ee-ab8f-2406cfd6ffd0
-- title:
--   Chunk budget on one AxNum/TabAt axis
-- statement:
--   On a single round-six axis carrying an `AxNum` package and a table-size fact `TabAt`, the chunk half of the axis budget holds at the uniform constant $K_{\mathrm{ch}}$.
--
--   Fix a plan $ap$ with `ChunkPlan6` and `ChunkPlanB`, and an axis with $d_P(n)=D+1$. Combining the Proved size package `chunk_facts`, the natural cost bound `chunk_cost_nat`, and the real comparison `cY_le`, one obtains
--   $$
--   \texttt{ChunkBudgetAt}\ P\ ap\ n\ src\ D\ k\ \bigl(K_{\mathrm{ch}}(P,ap)\cdot cU_6(P,n,2)/(D+1)\bigr).
--   $$
--   The comparison uses $d+\ell\le N_{\mathrm{cost}}$ and the definition $cU_6(P,n,2)=T_P\cdot p\cdot N_{\mathrm{cost}}\cdot(\log\lg n+1)^2$.
-- source:
--   xuanji round-six (Solutions.J6SegAxBud7); consumes Proved J6Seg.ChB.chunk_facts / chunk_cost_nat / cY_le; feeds chunkBudget6_all

import Definitions.Def_IntMul_Kappa_R6_Defs70

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open J6Seg J6Seg.ChB
open IntMul NLogN NLogN.KIL NLogN.KFB IntMul.Kappa.R6 J6Seg J6Seg.KR
variable {P : Prm} {n : ℕ} {src : ℕ → ℕ} {D k : ℕ} (ap : AxPlan6) (h : Side.AxNum P n src D k)
include h

theorem J6Seg.ChB.chunk_budget_at (hT : J6Seg.Ax.TabAt P n src k) (hc : AxCh.ChunkPlan6 ap) (hcb : ChunkPlanB ap)
    (hD : dP6 P n = D + 1) :
    ChunkBudgetAt P ap n src D k (Kch P ap * cU6 P n 2 / (D + 1)) := by sorry
