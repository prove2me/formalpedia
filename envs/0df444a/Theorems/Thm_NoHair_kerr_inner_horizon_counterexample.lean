-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_counterexample
-- name    : NoHair.kerr_inner_horizon_counterexample
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:54:32.150396+00:00
-- url     : https://prove2.me/theorems/c4698ceb-01fb-4c66-997c-a1115474b338
-- title:
--   An inner-horizon end in the analytic vacuum uniqueness statement
-- statement:
--   Choose the end of the ingoing $m=5/2$, $a=2$ vacuum Kerr spacetime to be the whole coordinate region $r>1$. The two roots of $\Delta$ are $1$ and $4$. Relative to this end the domain of outer communications is $r>1$ and the future event horizon is the nondegenerate inner Killing horizon $r=1$. The relative domain includes $r=2$ between the horizons, where no complete unit-speed timelike observer can pass. This gives a proposed counterexample to the formal analytic vacuum milestone, whose end predicate permits this choice. The classical uniqueness theorem uses the asymptotic end near infinity.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§5 and 9, equations (32)–(38) and (88)–(94), https://arxiv.org/abs/0706.0622. E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22, 3 (2019), §§2–3 on limit curves, causal convexity, and global hyperbolicity, https://doi.org/10.1007/s41114-019-0019-x. The choice of an end reaching the inner horizon is a proposed counterexample using the mission's definition of a stationary asymptotically flat end.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_horizon_counterexample :
    let g := (kerrNewmanMetricField (5/2) 2 0)
    let F := (kerrNewmanFieldField 2 0)
    ∃ (T : VecField (kerrNewmanSpacetime 2)) (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
      (E : AsymptoticallyFlatEnd g F φ),
      IsStationaryBlackHole g F T φ E ∧ (∀ x, F x = 0) ∧ IsAnalyticBilinField g ∧
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) ∧
      ¬ ∃ μ b : ℝ, IsKerrNewmanBlackHoleParams μ b 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) μ b 0 := by
  sorry
