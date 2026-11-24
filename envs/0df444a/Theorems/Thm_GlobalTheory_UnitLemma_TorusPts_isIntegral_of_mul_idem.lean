-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TorusPts_isIntegral_of_mul_idem
-- name    : GlobalTheory.UnitLemma.TorusPts.isIntegral_of_mul_idem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:15.214947+00:00
-- url     : https://prove2.me/theorems/4b11d631-2839-4e63-98c6-78e5bc5a8c06
-- title:
--   Torus Pts: is Integral of mul idem
-- statement:
--   The Torus Pts construction uses the is Integral of mul idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInjectiveTorusClassesOfIdempotentDecomposi.lean#L64-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsInjectiveTorusClassesOfIdempotentDecomposi.lean#L64-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyDvdPowOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInjectiveTorusClassesOfIdempotentDecomposi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TorusPts

theorem GlobalTheory.UnitLemma.TorusPts.isIntegral_of_mul_idem {K : UQ} (B : InvAlg K) {f : B.A} (hf : f * f = f) (h0 : f ≠ 0) (x : K.E)
    (hx : IsIntegral K.O (algebraMap K.E B.A x * f)) : IsIntegral K.O x := by sorry
