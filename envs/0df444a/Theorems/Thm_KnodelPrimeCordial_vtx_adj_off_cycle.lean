-- Prove2me | Theorems.Thm_KnodelPrimeCordial_vtx_adj_off_cycle
-- name    : KnodelPrimeCordial.vtx_adj_off_cycle
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T08:19:07.648031+00:00
-- url     : https://prove2.me/theorems/68600c58-de6f-4a98-9323-22956676f05c
-- title:
--   Edges outside the named cycle are exactly the even-index chords
-- statement:
--   Let $n\ge8$ be even, and let $a,b$ be indices that are not consecutive in either cyclic direction. Then $v_a$ and $v_b$ are adjacent in $W_{3,n}$ if and only if they are distinct and either $a$ is even with $b\equiv a+5\pmod n$, or $b$ is even with $a\equiv b+5\pmod n$. This identifies precisely the edges remaining after the cycle edges are removed.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026), §1 p.3, cyclic edge-set display. Supporting lemma extracted from the cyclic_model milestone.

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_cyc
import Definitions.Def_KnodelPrimeCordial_vtx

theorem KnodelPrimeCordial.vtx_adj_off_cycle (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) (a b : Fin n) (hab : b.val ≠ (a.val + 1) % n)
    (hba : a.val ≠ (b.val + 1) % n) :
    (knodel 3 n).Adj (vtx n (by omega) a) (vtx n (by omega) b) ↔
      a ≠ b ∧ ((Even a.val ∧ b.val = (a.val + 5) % n) ∨
        (Even b.val ∧ a.val = (b.val + 5) % n)) := by sorry
