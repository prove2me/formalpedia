-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryChart_hasStrictFDerivAt_ofFn_prod
-- name    : GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:35.567802+00:00
-- url     : https://prove2.me/theorems/023dcc8b-51ef-4cca-b491-19495a2b05e6
-- title:
--   Unitary Chart: has Strict FDeriv At of Fn prod
-- statement:
--   The Unitary Chart construction uses the has Strict FDeriv At of Fn prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupSecondKindCoordinatesNearOne.lean#L8-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupSecondKindCoordinatesNearOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.UnitaryChart
open Topology Filter

theorem GlobalTheory.UnitaryChart.hasStrictFDerivAt_ofFn_prod {F E : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedRing E] [NormedAlgebra ℝ E] :
    ∀ (N : ℕ) (g : Fin N → F → E) (g' : Fin N → F →L[ℝ] E),
      (∀ i, g i 0 = 1 ∧ HasStrictFDerivAt (g i) (g' i) 0) →
      (List.ofFn fun i => g i 0).prod = 1 ∧
        HasStrictFDerivAt (fun t => (List.ofFn fun i => g i t).prod) (∑ i, g' i) 0 := by sorry
