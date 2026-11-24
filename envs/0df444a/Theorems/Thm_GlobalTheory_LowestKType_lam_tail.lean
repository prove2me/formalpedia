-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_lam_tail
-- name    : GlobalTheory.LowestKType.lam_tail
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:33.029866+00:00
-- url     : https://prove2.me/theorems/be5b6aa9-17d0-44d0-bc2b-1fd26e718d69
-- title:
--   Lowest KType: lam tail
-- statement:
--   The Lowest KType construction uses the lam tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L22-L27

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

theorem GlobalTheory.LowestKType.lam_tail (h : D.Hyp) (c : ℕ) : D.lam (D.p + c) = -D.b (D.j + c) := by sorry
