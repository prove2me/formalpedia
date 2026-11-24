-- Prove2me | Theorems.Thm_GlobalTheory_wittVector_coeff_add_pow_mul
-- name    : GlobalTheory.wittVector_coeff_add_pow_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:40.444534+00:00
-- url     : https://prove2.me/theorems/7973bf4c-0d34-42b4-b441-2b932f50812e
-- title:
--   Global Theory: witt Vector coeff add pow mul
-- statement:
--   The Global Theory construction uses the witt Vector coeff add pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdeal.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WittVectorDvdOfSaturatedIdeal.lean#L25-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorDvdOfSaturatedIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WittVector

theorem GlobalTheory.wittVector_coeff_add_pow_mul {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] (x t : WittVector l R) (m j : ℕ) (hj : j < m) :
    (x + (l : WittVector l R) ^ m * t).coeff j = x.coeff j := by sorry
