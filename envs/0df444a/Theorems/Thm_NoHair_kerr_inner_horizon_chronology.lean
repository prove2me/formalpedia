-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_chronology
-- name    : NoHair.kerr_inner_horizon_chronology
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:58:28.866122+00:00
-- url     : https://prove2.me/theorems/756e5385-e702-4848-aa1d-d7d2af3e054c
-- title:
--   Chronological past of the region above the inner Kerr horizon
-- statement:
--   In the ingoing positive-radius Kerr spacetime of mass $5/2$ and spin $2$, equip the metric with its canonical future time direction. The region $A=\{r>1\}$ is its own chronological past and lies in its chronological future. Every timelike curve attempting to cross $r=1$ outwards encounters a strictly inward radial derivative on the inner Killing horizon. Every point of the open region has a nearby timelike predecessor and a nearby timelike successor in that region.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§4–5 and 9, in particular equations (107)–(115), https://arxiv.org/abs/0706.0622. E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x. These statements apply the causal structure to the formal choice of inner-horizon end.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set

theorem NoHair.kerr_inner_horizon_chronology :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    chronoPastSet g T A = A ∧ A ⊆ chronoFutureSet g T A := by
  sorry
