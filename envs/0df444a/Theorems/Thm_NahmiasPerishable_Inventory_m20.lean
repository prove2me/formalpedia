-- Prove2me | Theorems.Thm_NahmiasPerishable_Inventory_m20
-- name    : NahmiasPerishable.Inventory.m20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:26:39.007978+00:00
-- url     : https://prove2.me/theorems/f441b93d-8a26-4fff-bb1f-1a8eb76976f5
-- title:
--   Constant-demand exponential-decay solution
-- statement:
--   dI(t)/dt + θI(t) = −D(t).
--   When D(t) = λ, independent of t, the solution obtained is
--   I(t + u) = exp(−θu)·[I(t) + λ/θ] − λ/θ.
--
--   Differences from the source:
--   - encoding: the balance ODE between replenishments → an arbitrary real interval with continuous physical inventory and the ODE on its interior; reason: endpoints and u=0 are included; no stock trajectory is extended physically past depletion
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, Operations Research 30(4), §2.2.a, Constant-demand exponential-decay solution (unnumbered), p. 698 (PDF 19), DOI:10.1287/opre.30.4.680; review attribution: Ghare and Schrader [1963].

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open Set

namespace NahmiasPerishable.Inventory

theorem m20 (I : ℝ → ℝ) (theta rate t u : ℝ) (htheta : 0 < theta)
    (hrate : 0 ≤ rate) (hu : 0 ≤ u) (hI : ContinuousOn I (Icc t (t+u)))
    (hphysical : ∀ v ∈ Icc t (t+u), 0 ≤ I v)
    (hode : ∀ v ∈ Ioo t (t+u), HasDerivAt I (-rate-theta*I v) v) :
    I (t+u) = Real.exp (-theta*u)*(I t+rate/theta)-rate/theta := by sorry

end NahmiasPerishable.Inventory
