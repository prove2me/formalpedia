-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_eq_zero_of_isNilpotent
-- name    : GlobalTheory.UnitLemma.Centraliser.eq_zero_of_isNilpotent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:33:11.707265+00:00
-- url     : https://prove2.me/theorems/ed94c6a0-f0bc-4e31-ac6c-a81c334d36b7
-- title:
--   Centraliser: eq zero of is Nilpotent
-- statement:
--   The Centraliser construction uses the eq zero of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L75-L81

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

theorem GlobalTheory.UnitLemma.Centraliser.eq_zero_of_isNilpotent {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : IsNilpotent a) : a = 0 := by sorry
