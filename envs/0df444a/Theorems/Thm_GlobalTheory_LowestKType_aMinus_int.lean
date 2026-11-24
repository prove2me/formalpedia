-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_aMinus_int
-- name    : GlobalTheory.LowestKType.aMinus_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:16:59.579663+00:00
-- url     : https://prove2.me/theorems/8e46cb5c-bf34-4f35-a85c-99f57998e32a
-- title:
--   Lowest KType: a Minus int
-- statement:
--   The Lowest KType construction uses the a Minus int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L59-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L59-L66

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

theorem GlobalTheory.LowestKType.aMinus_int (h : D.Hyp) (s : ℕ) : ∃ z : ℤ, D.aMinus s = z := by sorry
