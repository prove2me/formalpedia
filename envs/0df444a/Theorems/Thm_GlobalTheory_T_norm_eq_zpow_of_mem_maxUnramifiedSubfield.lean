-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_eq_zpow_of_mem_maxUnramifiedSubfield
-- name    : GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:53:27.720804+00:00
-- url     : https://prove2.me/theorems/7d133d86-9bfd-4240-a6f7-6ce0d78a09fd
-- title:
--   T: norm eq zpow of mem max Unramified Subfield
-- statement:
--   The T construction uses the norm eq zpow of mem max Unramified Subfield property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfieldStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormEqZpowOfMemMaxUnramifiedSubfieldStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfield
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : Om l), x ∈ K0 K → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ n := by sorry
