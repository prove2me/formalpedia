-- Prove2me | Theorems.Thm_Kyprianou_Ch02_identDistribPairOfAELimitsV1
-- name    : Kyprianou.Ch02.identDistribPairOfAELimitsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:33:26.222984+00:00
-- url     : https://prove2.me/theorems/f0e53362-9914-41d7-a2d0-0be15643afc3
-- title:
--   Equality in distribution of pair-valued random variables passes to almost sure limits
-- statement:
--   Obtain almost-everywhere measurability of the limits, then use Mathlib tendstoInDistribution_of_ae_tendsto on both sequences. The sequences of probability measures are equal by IdentDistrib, so uniqueness of limits gives equality.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.identDistribPairOfAELimitsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : ℕ → Ω → ℝ × ℝ) (f g : Ω → ℝ × ℝ)
    (hLaw : ∀ n, IdentDistrib (F n) (G n) P P)
    (hf : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (f ω)))
    (hg : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (g ω))) :
    IdentDistrib f g P P := by sorry
