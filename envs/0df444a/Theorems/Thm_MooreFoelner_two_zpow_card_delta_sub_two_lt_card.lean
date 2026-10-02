-- Prove2me | Theorems.Thm_MooreFoelner_two_zpow_card_delta_sub_two_lt_card
-- name    : MooreFoelner.two_zpow_card_delta_sub_two_lt_card
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-02T00:50:32.470226+00:00
-- url     : https://prove2.me/theorems/bb74fc18-8fa9-442e-85ee-c2d2dabb3fd9
-- title:
--   Lemma 5.4 — if ∂T has n leaves then T has more than 2^(n−2)
-- statement:
--   For every tree $T$, $|T| > 2^{n-2}$, where $n = |\partial T|$.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 13, Lemma 5.4

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem two_zpow_card_delta_sub_two_lt_card (T : Finset Seq) (hT : IsTree T) :
    (2 : ℝ) ^ (((delta T).card : ℤ) - 2) < T.card := by
  sorry

end MooreFoelner
