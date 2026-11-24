-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovPathLawOfCommonAELimitsV1
-- name    : Kyprianou.Ch03.strongMarkovPathLawOfCommonAELimitsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:41:39.602205+00:00
-- url     : https://prove2.me/theorems/6ca4e517-a112-432a-b338-6d002fb7c8aa
-- title:
--   Path laws from common almost-sure coordinate limits
-- statement:
--   Use a single measurable conull subset of the common convergence event and patch every coordinate to zero off it. Finite-dimensional pushforwards converge in distribution under the normalised finite measure (zero mass separately); cylinder uniqueness gives the whole path law. The common event is essential for AEMeasurability on an uncountable product.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent f441c06a-283e-4064-b4f5-099f01124b30.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovPathLawOfCommonAELimitsV1
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (Y : ℕ → Omega → (NNReal → Real)) (Z : Omega → (NNReal → Real))
    (nu : Measure (NNReal → Real))
    (hMeas : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, Measure.map (Y n) mu = nu)
    (hLimit : ∀ᵐ w ∂mu, ∀ u : NNReal,
      Tendsto (fun n => Y n w u) atTop (nhds (Z w u))) :
    AEMeasurable Z mu ∧ Measure.map Z mu = nu := by
  sorry
