-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_gsum_eq_add_gsum_update
-- name    : GlobalTheory.PMonE.gsum_eq_add_gsum_update
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:28.878384+00:00
-- url     : https://prove2.me/theorems/09bdf10a-0297-47f7-88af-941b7a843844
-- title:
--   PMon E: gsum eq add gsum update
-- statement:
--   The PMon E construction uses the gsum eq add gsum update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueIntegralAdditiveSystemFrobeniusPower.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUniqueIntegralAdditiveSystemFrobeniusPower.lean#L37-L43

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

theorem GlobalTheory.PMonE.gsum_eq_add_gsum_update {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]
    (q D : ℕ) (U : ℕ → Matrix m m F) (y : m → F) :
    gsum q D U y = y + gsum q D (fun n => if n = 0 then U 0 - 1 else U n) y := by sorry
