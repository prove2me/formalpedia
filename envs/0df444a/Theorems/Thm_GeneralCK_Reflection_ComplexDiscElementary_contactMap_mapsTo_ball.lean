-- Prove2me | Theorems.Thm_GeneralCK_Reflection_ComplexDiscElementary_contactMap_mapsTo_ball
-- name    : GeneralCK.Reflection.ComplexDiscElementary.contactMap_mapsTo_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:03:36.689278+00:00
-- url     : https://prove2.me/theorems/0669be31-8c46-4000-9a91-4bf0c393a018
-- title:
--   The scaled complex contact map stays strictly inside its disc
-- statement:
--   Let $D=\{c\in\mathbb C:|c|\le4/5\}$, let $E:\mathbb C\to\mathbb C$ be any function, and let $\tau\in\mathbb C$. Suppose $|\tau|\le7/10$ and $|E(c)|\le1103/1000$ for every $c\in D$. The contact map $T(c)=\tau E(c)$ then satisfies $$T(D)\subset\{c\in\mathbb C:|c|<4/5\}.$$ This exact numerical margin supports the later complex-contact construction; the bound on $E$ is an explicit premise.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexDiscElementary.lean#L58-L69

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_GeneralCK_complex_contact

open GeneralCK.Reflection.ComplexDiscElementary
open Set

theorem GeneralCK.Reflection.ComplexDiscElementary.contactMap_mapsTo_ball
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
      (Metric.ball 0 (4 / 5 : ℝ)) := by sorry
