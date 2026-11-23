-- Prove2me | Theorems.Thm_GlobalTheory_finrank_pos_of_isIrreducible
-- name    : GlobalTheory.finrank_pos_of_isIrreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:52.3578+00:00
-- url     : https://prove2.me/theorems/f73ccb05-0963-4e8a-9673-d4491e5d7878
-- title:
--   Global Theory: finrank pos of is Irreducible
-- statement:
--   The Global Theory construction uses the finrank pos of is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L134-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
variable [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
omit [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K]

theorem GlobalTheory.finrank_pos_of_isIrreducible [h : ρ.IsIrreducible] : 0 < Module.finrank ℂ V := by sorry
