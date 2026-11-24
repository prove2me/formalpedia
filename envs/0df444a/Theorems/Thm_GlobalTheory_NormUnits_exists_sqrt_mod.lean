-- Prove2me | Theorems.Thm_GlobalTheory_NormUnits_exists_sqrt_mod
-- name    : GlobalTheory.NormUnits.exists_sqrt_mod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:55.106072+00:00
-- url     : https://prove2.me/theorems/030a6203-6c5c-4519-885c-493690e3279d
-- title:
--   Norm Units: exists sqrt mod
-- statement:
--   The Norm Units construction uses the exists sqrt mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean#L135-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TotalDegreeCMulXMulX.lean#L135-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormUnits
variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GlobalTheory.NormUnits.exists_sqrt_mod [LocallyCompactSpace K] (t : K) (ht : ‖t‖ ≤ 1) (h2 : ‖(2 : K)‖ < 1) :
    ∃ r : K, ‖r‖ ≤ 1 ∧ ‖r ^ 2 - t‖ < 1 := by sorry
