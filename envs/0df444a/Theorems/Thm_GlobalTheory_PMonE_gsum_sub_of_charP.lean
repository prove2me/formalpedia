-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_gsum_sub_of_charP
-- name    : GlobalTheory.PMonE.gsum_sub_of_charP
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:52.392153+00:00
-- url     : https://prove2.me/theorems/76363588-4cf5-4303-9cea-69a68f8eaa17
-- title:
--   PMon E: gsum sub of char P
-- statement:
--   The PMon E construction uses the gsum sub of char P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueIntegralAdditiveSystemFrobeniusPower.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueIntegralAdditiveSystemFrobeniusPower.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE Finset
open GlobalTheory GlobalTheory.PMonE

theorem GlobalTheory.PMonE.gsum_sub_of_charP {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] {m : Type*} [Fintype m]
    (e D : ℕ) (M : ℕ → Matrix m m F) (x y : m → F) :
    gsum (p ^ e) D M (x - y) = gsum (p ^ e) D M x - gsum (p ^ e) D M y := by sorry
