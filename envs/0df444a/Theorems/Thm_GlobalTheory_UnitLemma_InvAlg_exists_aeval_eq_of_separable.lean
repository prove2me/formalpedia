-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_InvAlg_exists_aeval_eq_of_separable
-- name    : GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:38:06.037356+00:00
-- url     : https://prove2.me/theorems/c59d03f5-ca4b-49af-9a57-262b1c41a7c0
-- title:
--   Inv Alg: exists aeval eq of separable
-- statement:
--   The Inv Alg construction uses the exists aeval eq of separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfCharpolySeparableInvolution.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsAevalEqOfCharpolySeparableInvolution.lean#L46-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by sorry
