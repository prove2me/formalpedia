-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_weightData_t_odd
-- name    : GlobalTheory.LowestKType.weightData_t_odd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:04.702667+00:00
-- url     : https://prove2.me/theorems/b52a1b6f-a21b-4ebe-92fa-3be4aa4d85f4
-- title:
--   Lowest KType: weight Data t odd
-- statement:
--   The Lowest KType construction uses the weight Data t odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L46-L48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_IndefiniteWeightData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LamGeoEqFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LowestKType
open Formalism.IndefR.IndefiniteWeightData Formalism.IndefR.IndefiniteWeightData.WeightData
variable {D : WeightData}

theorem GlobalTheory.LowestKType.weightData_t_odd (h : D.Hyp) : ∃ w : ℕ, (D.t : ℚ) = 2 * w + 1 := by sorry
