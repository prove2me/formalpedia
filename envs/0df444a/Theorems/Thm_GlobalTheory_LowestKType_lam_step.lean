-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_lam_step
-- name    : GlobalTheory.LowestKType.lam_step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:14:33.817708+00:00
-- url     : https://prove2.me/theorems/1aefe79d-b675-45e1-ab69-acc6cde6ff40
-- title:
--   Lowest KType: lam step
-- statement:
--   The Lowest KType construction uses the lam step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L29-L32

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

theorem GlobalTheory.LowestKType.lam_step (h : D.Hyp) (i : ℕ) (h1 : 1 ≤ i) (h2 : i < D.r) :
    (D.lam (i + 1) : ℚ) + 1 ≤ D.lam i := by sorry
