-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FourierJacobiAverage_app_coe
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:39.72447+00:00
-- url     : https://prove2.me/theorems/ca582c07-6e5d-4df3-b5ae-7b05f6851e9f
-- title:
--   Fourier Jacobi Average: app coe
-- statement:
--   The Fourier Jacobi Average construction uses the app coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/FourierJacobiAverage.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/FourierJacobiAverage.lean#L51-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (l : SB X →ₗ[ℂ] V) (f : SB X) : app l (f : X → ℂ) = l f := by sorry
