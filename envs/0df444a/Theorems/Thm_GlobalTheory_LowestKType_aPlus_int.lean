-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_aPlus_int
-- name    : GlobalTheory.LowestKType.aPlus_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:18:55.193612+00:00
-- url     : https://prove2.me/theorems/531220f6-b0e1-48a5-8487-664149caad1e
-- title:
--   Lowest KType: a Plus int
-- statement:
--   The Lowest KType construction uses the a Plus int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L50-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L50-L57

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

theorem GlobalTheory.LowestKType.aPlus_int (h : D.Hyp) (i : ℕ) : ∃ z : ℤ, D.aPlus i = z := by sorry
