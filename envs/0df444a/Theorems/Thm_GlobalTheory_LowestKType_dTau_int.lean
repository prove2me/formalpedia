-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_dTau_int
-- name    : GlobalTheory.LowestKType.dTau_int
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:16:53.588851+00:00
-- url     : https://prove2.me/theorems/ac657df8-198a-4315-a140-303fe9d270bc
-- title:
--   Lowest KType: d Tau int
-- statement:
--   The Lowest KType construction uses the d Tau int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L93-L97

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

theorem GlobalTheory.LowestKType.dTau_int (h : D.Hyp) : ∃ z : ℤ, D.dTau = z := by sorry
