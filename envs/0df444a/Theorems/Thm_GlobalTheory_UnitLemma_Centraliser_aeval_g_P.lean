-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_aeval_g_P
-- name    : GlobalTheory.UnitLemma.Centraliser.aeval_g_P
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:38.206784+00:00
-- url     : https://prove2.me/theorems/14027947-93d1-460e-a237-384991ce5e22
-- title:
--   Centraliser: aeval g P
-- statement:
--   The Centraliser construction uses the aeval g P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L48-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Centraliser

theorem GlobalTheory.UnitLemma.Centraliser.aeval_g_P {K : UQ} (B : InvAlg K) : aeval B.g B.P = 0 := by sorry
