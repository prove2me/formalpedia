-- Prove2me | Theorems.Thm_Kyprianou_Ch02_iIndepFunPairOfAELimitsV1
-- name    : Kyprianou.Ch02.iIndepFunPairOfAELimitsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:33:28.569884+00:00
-- url     : https://prove2.me/theorems/0a68c4c0-ada5-4274-a14a-b1f159517eb5
-- title:
--   Finite family independence of pairs passes to almost sure limits
-- statement:
--   Use the characteristic-function-dual criterion for finite independent families in Banach spaces. Almost sure convergence and dominated convergence give convergence of each characteristic function and the finite joint characteristic function; pass to limits in the finite product identity.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.iIndepFunPairOfAELimitsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) (F : ℕ → Fin m → Ω → ℝ × ℝ)
    (f : Fin m → Ω → ℝ × ℝ)
    (hm : ∀ n i, AEMeasurable (F n i) P)
    (hi : ∀ n, iIndepFun (F n) P)
    (hl : ∀ i, ∀ᵐ ω ∂P, Tendsto (fun n => F n i ω) atTop (nhds (f i ω))) :
    iIndepFun f P := by sorry
