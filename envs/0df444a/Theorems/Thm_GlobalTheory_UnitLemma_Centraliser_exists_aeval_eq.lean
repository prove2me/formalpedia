-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_exists_aeval_eq
-- name    : GlobalTheory.UnitLemma.Centraliser.exists_aeval_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:23.157064+00:00
-- url     : https://prove2.me/theorems/35e63dcd-2f94-4f34-b7ee-ffd9762dae72
-- title:
--   Centraliser: exists aeval eq
-- statement:
--   The Centraliser construction uses the exists aeval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L54-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L54-L73

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

theorem GlobalTheory.UnitLemma.Centraliser.exists_aeval_eq {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (y : B.A) :
    ∃ p : K.E[X], aeval B.g p = y := by sorry
