-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_frobPerm_pow_apply
-- name    : GlobalTheory.PMonE.frobPerm_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:28.542654+00:00
-- url     : https://prove2.me/theorems/2523da61-6ca6-469b-b362-36bb89cad4b4
-- title:
--   PMon E: frob Perm pow apply
-- statement:
--   The PMon E construction uses the frob Perm pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardWindowZerosInnerEqShiftedOuter.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardWindowZerosInnerEqShiftedOuter.lean#L17-L21

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

theorem GlobalTheory.PMonE.frobPerm_pow_apply (n : ℕ) (x : F) : (frobPerm (F := F) p ^ n) x = x ^ p ^ n := by sorry
