-- Prove2me | Theorems.Thm_GlobalTheory_prod_add_ite_shift
-- name    : GlobalTheory.prod_add_ite_shift
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:54.551975+00:00
-- url     : https://prove2.me/theorems/252c554e-2d82-436c-98d5-ac3ce591b1e1
-- title:
--   Global Theory: prod add ite shift
-- statement:
--   The Global Theory construction uses the prod add ite shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QuantumDetVectorMultiplierShiftPlus.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QuantumDetVectorMultiplierShiftPlus.lean#L12-L20

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliLeftComatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliDetMulVectorTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorPolyMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QminorIntertwiningApplyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsEigenSplitOfResolventIdentityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QuantumDetVectorMultiplierShiftPlus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory

theorem GlobalTheory.prod_add_ite_shift {n : ℕ} (ν : Fin n → ℂ) (s : Fin n) (u : ℂ) :
    (∏ t, (u + ν t + if t = s then 1 else 0)) =
      (∏ t, (u + ν t)) + ∏ t ∈ Finset.univ.erase s, (u + ν t) := by sorry
