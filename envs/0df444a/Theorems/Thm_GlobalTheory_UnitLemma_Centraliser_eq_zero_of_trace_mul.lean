-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Centraliser_eq_zero_of_trace_mul
-- name    : GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:32:28.175144+00:00
-- url     : https://prove2.me/theorems/5d1b4d6b-14bf-4a2d-9cd2-a1e1c6f54224
-- title:
--   Centraliser: eq zero of trace mul
-- statement:
--   The Centraliser construction uses the eq zero of trace mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L83-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyDvdPowOfAevalEqZero.lean#L83-L95

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

theorem GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (a : B.A)
    (ha : ∀ y, Algebra.trace K.E B.A (a * y) = 0) : a = 0 := by sorry
