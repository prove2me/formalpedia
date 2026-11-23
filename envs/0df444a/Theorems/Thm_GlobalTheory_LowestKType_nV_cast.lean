-- Prove2me | Theorems.Thm_GlobalTheory_LowestKType_nV_cast
-- name    : GlobalTheory.LowestKType.nV_cast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:07.245426+00:00
-- url     : https://prove2.me/theorems/3b85de11-d262-47c1-b2e7-f0a2be3330ae
-- title:
--   Lowest KType: n V cast
-- statement:
--   The Lowest KType construction uses the n V cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LamGeoEqFormula.lean#L19-L20

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

theorem GlobalTheory.LowestKType.nV_cast (h : D.Hyp) : (D.nV : ℚ) = D.p + D.q + D.t := by sorry
