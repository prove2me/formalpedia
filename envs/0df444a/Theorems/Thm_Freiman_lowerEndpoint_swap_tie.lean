-- Prove2me | Theorems.Thm_Freiman_lowerEndpoint_swap_tie
-- name    : Freiman.lowerEndpoint_swap_tie
-- status  : Disproved
-- author  : @Koki Yamada
-- created : 2026-09-16T11:13:35.602614+00:00
-- url     : https://prove2.me/theorems/a7917e14-4595-42fc-a63c-d4b45f2eabff
-- title:
--   Freiman: continued-fraction endpoints of a width-tie swap
-- statement:
--   If two continued-fraction sides have equal $\alpha$--$\beta$ width, swapping them does not change either endpoint scalar. The endpoint of a pair is $4$ plus the two prefix evaluations of $\tau$ on the endpoint words; at a width tie both presentations are left-wide, and the resulting word pairs still yield the same sum.
--
--   $$
--   \mathrm{width}(a)=\mathrm{width}(b)\quad\Longrightarrow\quad \mathrm{lowerEndpoint}(a,b,u)=\mathrm{lowerEndpoint}(b,a,u).
--   $$
-- source:
--   Freiman report, §15, printed source pages 140–144; width-tie case of the swapped fork identity Freiman.late_fork_endpoints_swapped.

import Definitions.Def_Freiman_lateGeometry
import Mathlib.Tactic

set_option maxRecDepth 8000
set_option maxHeartbeats 0

open Freiman

theorem Freiman.lowerEndpoint_swap_tie (a b : List ℕ+) (u : Bool) (h : lowerWidth a = lowerWidth b) : lowerEndpoint (a, b) u = lowerEndpoint (b, a) u := by
  sorry
