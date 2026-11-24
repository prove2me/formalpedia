-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_pw_eq_zpow
-- name    : GlobalTheory.PMonE.pw_eq_zpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:44.599605+00:00
-- url     : https://prove2.me/theorems/b54679bb-7846-4f35-936c-e5dcfefc72d4
-- title:
--   PMon E: pw eq zpow
-- statement:
--   The PMon E construction uses the pw eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardWindowZerosInnerEqShiftedOuter.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardWindowZerosInnerEqShiftedOuter.lean#L23-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowTEqRowS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardWindowZerosInnerEqShiftedOuter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p]

theorem GlobalTheory.PMonE.pw_eq_zpow (k : ℤ) (x : F) : pw p k x = (frobPerm (F := F) p ^ k) x := by sorry
