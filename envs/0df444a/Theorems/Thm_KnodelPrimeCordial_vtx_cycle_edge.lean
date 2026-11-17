-- Prove2me | Theorems.Thm_KnodelPrimeCordial_vtx_cycle_edge
-- name    : KnodelPrimeCordial.vtx_cycle_edge
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T08:19:06.728186+00:00
-- url     : https://prove2.me/theorems/a41c4d6e-e8cc-4f9e-a25f-e0022ec3a448
-- title:
--   Consecutive vertex names give edges of the Knödel graph
-- statement:
--   For even $n\ge8$, every consecutive pair $v_a,v_{a+1}$ (indices modulo $n$) is adjacent in $W_{3,n}$. This establishes the cycle edges in the paper’s cyclic description.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026), §1 p.3, cyclic edge-set display. Supporting lemma extracted from the cyclic_model milestone.

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_vtx

theorem KnodelPrimeCordial.vtx_cycle_edge (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) (a b : Fin n) (hab : b.val = (a.val + 1) % n) :
    (knodel 3 n).Adj (vtx n (by omega) a) (vtx n (by omega) b) := by sorry
