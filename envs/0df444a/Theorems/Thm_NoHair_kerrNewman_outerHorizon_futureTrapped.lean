-- Prove2me | Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
-- name    : NoHair.kerrNewman_outerHorizon_futureTrapped
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:32:00.289883+00:00
-- url     : https://prove2.me/theorems/c9973130-c829-4b75-bc23-b60ddc79d7b2
-- title:
--   The outer horizon traps future timelike curves in ingoing Kerr–Schild coordinates
-- statement:
--   For admissible Kerr–Newman parameters, the canonical Kerr–Schild future direction is a continuous timelike field throughout $r>0$. If a future timelike curve starts on or inside $r=r_+$, its endpoint also satisfies $r\le r_+$. This one-way barrier includes the extremal horizon.
-- source:
--   B. Carter, Global structure of the Kerr family of gravitational fields, Phys. Rev. 174 (1968), 1559–1571, https://doi.org/10.1103/PhysRev.174.1559. The barrier follows from the future-null radial normal at the outer horizon.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open scoped ContDiff Manifold
open NoHair Set

theorem NoHair.kerrNewman_outerHorizon_futureTrapped (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    let T := kerrNewmanTimeDirection m a e
    let g := kerrNewmanMetricField m a e
    let b := kerrNewmanOuterRadius m a e
    IsTimeOrientation g T ∧ ∀ γ : ℝ → kerrNewmanSpacetime a,
      IsFutureTimelikeCurveIn g T univ γ → ksRadius a (γ 0).val ≤ b → ksRadius a (γ 1).val ≤ b := by sorry
