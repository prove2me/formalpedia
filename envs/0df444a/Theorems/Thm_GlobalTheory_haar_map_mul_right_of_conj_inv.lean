-- Prove2me | Theorems.Thm_GlobalTheory_haar_map_mul_right_of_conj_inv
-- name    : GlobalTheory.haar_map_mul_right_of_conj_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:11.755626+00:00
-- url     : https://prove2.me/theorems/7f90a548-762e-49b2-8fc6-a5ad3b6054c2
-- title:
--   Global Theory: haar map mul right of conj inv
-- statement:
--   The Global Theory construction uses the haar map mul right of conj inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/HaarMapMulRightOfConjInv.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/HaarMapMulRightOfConjInv.lean#L8-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HaarMapMulRightOfConjInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.haar_map_mul_right_of_conj_inv :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) := by sorry
