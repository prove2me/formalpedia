-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_relative_causality
-- name    : NoHair.kerr_inner_horizon_relative_causality
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:54:22.073098+00:00
-- url     : https://prove2.me/theorems/4ae59cb3-c773-413f-a5e8-a2bcdf1d08bf
-- title:
--   Causal domain relative to the Kerr inner-horizon cutoff
-- statement:
--   In the positive-radius ingoing patch of Kerr with $m=5/2$ and $a=2$, write $A=\{r>1\}$. With the ingoing future orientation, $I^-(A)=A$, $A\subset I^+(A)$, and $A$ is globally hyperbolic. The level $r=1$ is the inner horizon. On $1<r<4$ the radius decreases on every future causal curve. Thus a causal diamond with endpoints in $A$ stays away from $r=1$. The time coordinate bounds spatial speeds through the Kerr–Schild cone inequality.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§5 and 9, equations (32)–(38) and (88)–(94), https://arxiv.org/abs/0706.0622. E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22, 3 (2019), §§2–3 on limit curves, causal convexity, and global hyperbolicity, https://doi.org/10.1007/s41114-019-0019-x. The choice of an end reaching the inner horizon is a proposed counterexample using the mission's definition of a stationary asymptotically flat end.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_horizon_relative_causality :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := (kerrNewmanMetricField (5/2) 2 0)
    ∃ T : VecField (kerrNewmanSpacetime 2), IsTimeOrientation g T ∧
      chronoPastSet g T A = A ∧ A ⊆ chronoFutureSet g T A ∧ IsGloballyHyperbolicOn g T A := by
  sorry
